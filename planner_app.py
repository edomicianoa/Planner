from flask import Flask, render_template, request, redirect, url_for, jsonify, session, flash, send_from_directory, send_file, get_flashed_messages
import pyodbc
import json
FLASK_CLIENT_IDENTIFIER = "fabrica_edu_hml"
import sys
from datetime import datetime, timedelta, date
from functools import wraps
from collections import defaultdict
import threading
import time
import paho.mqtt.client as mqtt
import io
import logging
import os
import random
#from logging.handlers import RotatingFileHandler
from concurrent_log_handler import ConcurrentRotatingFileHandler
import string
import re
import math
import queue
import csv
#import flattener
import unicodedata
import smtplib
import pandas as pd 
import logging
import json
import decimal
import base64
import numpy as np
from openpyxl.drawing.image import Image
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.utils import formataddr
from datetime import datetime, timedelta
from werkzeug.utils import secure_filename
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.security import check_password_hash
from werkzeug.exceptions import NotFound
from collections import defaultdict # No topo do arquivo
from flask import url_for # Certifique-se que 'url_for' está importado
from scheduler import iniciar_agendador_de_turnos, recarregar_agendamentos, scheduler
from itsdangerous import URLSafeTimedSerializer



class EstoqueInsuficienteError(Exception):
    """Exceção personalizada para erros de falta de estoque."""
    pass
    
logger = logging.getLogger(__name__)
logging.getLogger('apscheduler').setLevel(logging.DEBUG)
# ===== NOVO: Fila para mensagens MQTT =====
mqtt_message_queue = queue.Queue()

# Variável global para rastrear o último ID de turno conhecido pelo sistema
last_known_system_turn_id = None
# Em planner_app.py (no topo do arquivo)

# Armazena o último timestamp de pulso aceito para cada ID de máquina
last_pulse_timestamps = {} 

# Lock para garantir a segurança em acesso multi-thread a 'last_pulse_timestamps'
pulse_debounce_lock = threading.Lock() 


# Constantes para detecção de inatividade
ID_MOTIVO_PARADA_AUTOMATICA = 2  # ID para "Parada Não Identificada"
ID_MOTIVO_FORA_DE_TURNO = 1      # ID para "Fora de Turno"
# Pool de conexões
connection_pool = queue.Queue(maxsize=5)  # Máximo de 5 conexões no pool
pool_lock = threading.Lock()

# Constantes para detecção de inatividade
ID_MOTIVO_PARADA_AUTOMATICA = 2  # ID do motivo de parada automática na tabela TBL_MotivoParada (verificar no BD)

# Criar diretório de logs se não existir
log_dir = os.path.join(os.getcwd(), 'logs')
if not os.path.exists(log_dir):
    os.makedirs(log_dir)



# --- Configuração Simplificada de Logging ---
log_formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')

# Handler para o arquivo de logs
log_file_path = os.path.join(log_dir, f'planner_{datetime.now().strftime("%Y-%m-%d")}.log')
file_handler = ConcurrentRotatingFileHandler(log_file_path, "a", maxBytes=10*1024*1024, backupCount=10, encoding='utf-8', delay=True)
file_handler.setFormatter(log_formatter)

# Handler para o console (sem manipulação de stream)
console_handler = logging.StreamHandler(sys.stdout)
console_handler.setFormatter(log_formatter)

# Configura o logger principal da aplicação
logging.basicConfig(
    level=logging.INFO,
    handlers=[file_handler, console_handler]
)

# Silencia um pouco o log do Werkzeug (servidor do Flask) para focar nos seus logs
logging.getLogger('werkzeug').setLevel(logging.ERROR)

# Define o logger que você usará no resto do seu código
logger = logging.getLogger(__name__)


# Evitar erros na virada de turno
virada_turno_lock = threading.Lock()

app = Flask(__name__)
app.secret_key = 'sua_chave_secreta_segura' # Lembre-se de usar uma chave secreta forte em produção!
app.config['SESSION_COOKIE_NAME'] = 'fabrica_edu_hml'
# Conexão global REMOVIDA - todas as interações com o BD usarão o pool de conexões localmente nas funções.
# conn = pyodbc.connect(...)
# cursor = conn.cursor()

# Adicione esta configuração para o gerador de tokens
# A 'secret_key' é a mesma que você já usa para a sessão do Flask
s = URLSafeTimedSerializer(app.secret_key)
# Buffer global e lock (existente no seu arquivo)
buffer_agregado = defaultdict(int)
lock = threading.Lock()

##########################################################################DEF##########################################################
class DecimalEncoder(json.JSONEncoder):
    def default(self, o):
        if isinstance(o, decimal.Decimal):
            return float(o)
        return super(DecimalEncoder, self).default(o)
        
def conectar_bd():
    """
    Cria e retorna uma nova conexão com o banco de dados.
    Implementa retry com backoff exponencial.
    """
    max_tentativas = 5
    tentativa = 0
    delay = 3  # segundos
    
    while tentativa < max_tentativas:
        try:
            conn = pyodbc.connect(
                'DRIVER={ODBC Driver 17 for SQL Server};'
                'SERVER=localhost;' # Ajuste para o endereço do seu SQL Server
                'DATABASE=EDU_HML;'
                'UID=sa;'
                'PWD=planner123;'
                'Connection Timeout=30;'  # Timeout de 30 segundos
                'TrustServerCertificate=yes;'  # Confiança no certificado do servidor
            )
            
            # Testar a conexão
            cursor = conn.cursor()
            cursor.execute("SELECT 1")
            cursor.fetchone()
            cursor.close()
            
            logger.debug("Conexão com o banco de dados estabelecida com sucesso")
            return conn
        
        except pyodbc.Error as e:
            tentativa += 1
            logger.error(f"Tentativa {tentativa}/{max_tentativas} - Erro ao conectar ao banco de dados: {str(e)}")
            
            if tentativa < max_tentativas:
                # Backoff exponencial
                sleep_time = delay * (2 ** (tentativa - 1))
                logger.info(f"Aguardando {sleep_time} segundos antes de tentar novamente...")
                time.sleep(sleep_time)
            else:
                logger.error("Número máximo de tentativas de conexão atingido")
                raise

def inicializar_pool():
    """Inicializa o pool de conexões"""
    with pool_lock: # Garante que apenas um thread inicialize o pool
        try:
            if connection_pool.qsize() == 0 and not hasattr(app, 'pool_initialized'): # Evita reinicializar
                for _ in range(3):  # Iniciar com 3 conexões
                    conn = conectar_bd() # Usa a função que lida com retries
                    connection_pool.put(conn)
                app.pool_initialized = True # Marca que o pool foi inicializado
                logger.info(f"Pool de conexões inicializado com {connection_pool.qsize()} conexões")
        except Exception as e:
            logger.error(f"Erro ao inicializar pool de conexões: {str(e)}")

def obter_conexao():
    """Obtém uma conexão do pool ou cria uma nova se necessário"""
    with pool_lock: # Protege o acesso ao pool
        try:
            # Tentar obter uma conexão do pool
            if not connection_pool.empty():
                conn = connection_pool.get(block=False) # Non-blocking to try to get from pool immediately
                
                # Testar se a conexão ainda é válida
                try:
                    cursor = conn.cursor()
                    cursor.execute("SELECT 1")
                    cursor.fetchone()
                    cursor.close()
                    return conn
                except Exception as e: # Catch any exception, not just pyodbc.Error for robustness
                    logger.warning(f"Conexão do pool inválida ou fechada ({e}), criando nova conexão.")
                    try:
                        conn.close() # Ensure the old, bad connection is truly closed
                    except:
                        pass
                    return conectar_bd() # Create a new, fresh connection
            else:
                # Se o pool estiver vazio, criar uma nova conexão
                logger.info("Pool vazio, criando nova conexão.")
                return conectar_bd()
        except queue.Empty: # Catch the specific exception if get(block=False) fails
            logger.info("Pool vazio (fila vazia), criando nova conexão.")
            return conectar_bd()
        except Exception as e:
            logger.error(f"Erro ao obter conexão do pool: {str(e)}")
            return conectar_bd() # Fallback: always try to connect if pool issues

def devolver_conexao(conn):
    """Devolve uma conexão ao pool"""
    with pool_lock: # Protege o acesso ao pool
        try:
            # Verificar se a conexão ainda é válida antes de devolver
            cursor = conn.cursor()
            cursor.execute("SELECT 1")
            cursor.fetchone()
            cursor.close()
            
            # Se o pool não estiver cheio, devolver a conexão
            if connection_pool.qsize() < connection_pool.maxsize:
                connection_pool.put(conn)
            else:
                # Se o pool estiver cheio, fechar a conexão para liberar recursos
                conn.close()
        except Exception as e:
            # Se a conexão não for válida ou houver erro ao testar, fechar e não devolver ao pool
            logger.warning(f"Conexão inválida ao tentar devolver ao pool, fechando-a: {e}")
            try:
                conn.close()
            except:
                pass
                


# def _update_machine_status(conn_local, cursor_local, id_maquina, new_status, id_motivo_parada=None, obs_evento=''):
    # """
    # Função auxiliar para atualizar o status de uma máquina.
    # VERSÃO FINAL E ROBUSTA: Atualiza o status em TBL_ExecucaoOP e TBL_OrdemProducao de forma direta.
    # """
    # timestamp = datetime.now()
    # id_turno_atual = identificar_turno(conn_local, cursor_local)
    
    # new_record_id = None

    # cursor_local.execute("""
        # SELECT TOP 1 IDRegistroStatus, Status, IDMotivoParada
        # FROM TBL_StatusMaquina 
        # WHERE IDMaquina = ? AND DataHoraFim IS NULL
        # ORDER BY DataHoraRegistro DESC
    # """, id_maquina)
    # ultimo_status_db = cursor_local.fetchone()

    # # --- INÍCIO DA LÓGICA DE ATUALIZAÇÃO DE STATUS DA OP (VERSÃO REFORÇADA) ---
    # if new_status == 1 and ultimo_status_db and ultimo_status_db.Status == 0:
        # cursor_local.execute("SELECT IDMotivoParada FROM TBL_MotivoParada WHERE Codigo = '03'")
        # motivo_setup_row = cursor_local.fetchone()
        # id_motivo_setup = motivo_setup_row.IDMotivoParada if motivo_setup_row else -1

        # if ultimo_status_db.IDMotivoParada == id_motivo_setup:
            # logger.info(f"Máquina {id_maquina} saindo de SETUP. Iniciando atualização de status da OP.")
            
            # # 1. Encontrar a ID da ordem que está 'Em Setup' ANTES de qualquer alteração.
            # cursor_local.execute("SELECT IDOrdem FROM TBL_ExecucaoOP WHERE IDMaquina = ? AND Status = 'Em Setup'", (id_maquina,))
            # execucao_em_setup = cursor_local.fetchone()

            # if execucao_em_setup:
                # id_ordem_a_atualizar = execucao_em_setup.IDOrdem

                # # 2. Atualizar a tabela de execução (para o Dashboard) usando o ID encontrado.
                # cursor_local.execute("""
                    # UPDATE TBL_ExecucaoOP 
                    # SET Status = 'Em Execucao' 
                    # WHERE IDOrdem = ? AND IDMaquina = ? AND Status = 'Em Setup'
                # """, (id_ordem_a_atualizar, id_maquina))
                # logger.info(f"Status em TBL_ExecucaoOP atualizado para 'Em Execucao' para OP ID {id_ordem_a_atualizar}.")

                # # 3. Atualizar a tabela principal da ordem (para a Consulta de Ordens) usando o mesmo ID.
                # cursor_local.execute("SELECT IDStatus FROM TBL_StatusOrdemProducao WHERE NomeStatus = 'Em Execucao'")
                # status_exec_row = cursor_local.fetchone()
                # if status_exec_row:
                    # id_status_execucao = status_exec_row.IDStatus
                    # cursor_local.execute("""
                        # UPDATE TBL_OrdemProducao
                        # SET IDStatus = ?
                        # WHERE IDOrdem = ?
                    # """, (id_status_execucao, id_ordem_a_atualizar))
                    # logger.info(f"Status em TBL_OrdemProducao atualizado para {id_status_execucao} para OP ID {id_ordem_a_atualizar}.")
                # else:
                    # logger.error("Não foi possível encontrar o ID de status para 'Em Execucao'. A tabela TBL_OrdemProducao não foi atualizada.")
            # else:
                # logger.warning(f"Saindo de um status de setup na máquina {id_maquina}, mas nenhuma OP 'Em Setup' foi encontrada para atualizar.")
    # # --- FIM DA LÓGICA DE ATUALIZAÇÃO ---

    # if ultimo_status_db and ultimo_status_db.Status == new_status:
        # if (new_status == 0 and ultimo_status_db.IDMotivoParada == id_motivo_parada) or new_status == 1:
            # return ultimo_status_db.IDRegistroStatus

    # if ultimo_status_db:
        # cursor_local.execute("""
            # UPDATE TBL_StatusMaquina 
            # SET DataHoraFim = ?, DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, ?)
            # WHERE IDRegistroStatus = ?
        # """, timestamp, timestamp, ultimo_status_db.IDRegistroStatus)

    # sql_insert_base = "INSERT INTO TBL_StatusMaquina ({columns}) OUTPUT INSERTED.IDRegistroStatus VALUES ({placeholders})"
    
    # observacao_final = obs_evento
    # if new_status == 0 and id_motivo_parada:
        # try:
            # cursor_local.execute("SELECT Descricao FROM TBL_MotivoParada WHERE IDMotivoParada = ?", id_motivo_parada)
            # motivo_row = cursor_local.fetchone()
            # if motivo_row and motivo_row.Descricao:
                # observacao_final = motivo_row.Descricao
                # if obs_evento: observacao_final = f"{observacao_final} ({obs_evento})"
        # except Exception as e:
            # logger.error(f"Erro ao buscar descrição do motivo de parada {id_motivo_parada}: {e}")

    # if new_status == 1:
        # columns = "IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, ObsEvento"
        # placeholders = "?, ?, ?, ?, ?, ?"
        # params = (id_maquina, new_status, timestamp, timestamp, id_turno_atual, observacao_final)
    # else:
        # columns = "IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDMotivoParada, IDTurno, ObsEvento"
        # placeholders = "?, ?, ?, ?, ?, ?, ?"
        # id_motivo_parada_final = id_motivo_parada or ID_MOTIVO_PARADA_AUTOMATICA
        # params = (id_maquina, new_status, timestamp, timestamp, id_motivo_parada_final, id_turno_atual, observacao_final)

    # sql_insert_final = sql_insert_base.format(columns=columns, placeholders=placeholders)
    # new_record_id = cursor_local.execute(sql_insert_final, params).fetchval()

    # if new_status == 1:
        # cursor_local.execute("INSERT INTO TBL_EventoStatus (IDMaquina, Status, DataHoraEvento, ObsEvento) VALUES (?, ?, ?, ?)", id_maquina, new_status, timestamp, observacao_final)
    # else:
        # cursor_local.execute("INSERT INTO TBL_EventoStatus (IDMaquina, Status, DataHoraEvento, IDMotivoParada, ObsEvento) VALUES (?, ?, ?, ?, ?)", id_maquina, new_status, timestamp, id_motivo_parada, observacao_final)

    # logger.info(f"Status da máquina {id_maquina} atualizado (Novo ID de Registro: {new_record_id}).")
    # return new_record_id

def forcar_gravacao_consolidada(chave, conn_local, cursor_local):
    """
    Força a gravação de dados consolidados para o banco de dados.
    Recebe conn_local e cursor_local para usar a conexão existente.
    """
    with lock: # Protege o acesso ao buffer_agregado
        quantidade = buffer_agregado.get(chave, 0)
        if quantidade > 0:
            try:
                cursor_local.execute("""
                    INSERT INTO VW_EventoProducaoComCicloReal (
                        IDExecucao, IDMaquina, IDTipoRecurso, IDOrdemProducao,
                        IDTurno, IDOperador, IDTipoEvento, Quantidade,
                        TipoValor, OrigemEvento, DataHoraEvento
                    )
                    VALUES (?, ?, ?, ?, ?, ?, 1, ?, 'BOA', 'AUTOMATICO', GETDATE())
                """, (*chave, quantidade))
                conn_local.commit()
                buffer_agregado.pop(chave, None)
                logger.info(f"Produção consolidada gravada por evento externo — chave: {chave}")
            except Exception as e:
                logger.error(f"Erro ao gravar consolidado: {e}")
                # Rollback não é feito aqui, pois o commit/rollback é do pool da rota que chamou.
                # Se esta função for chamada por um thread separado, ela precisa ter seu próprio try/except/finally de conexão.

def gravar_buffer_agrupado():
    """
    Grava os dados agrupados do buffer para o banco de dados.
    Esta função roda em um thread separado e gerencia sua própria conexão.
    """
    conn_local = None
    try:
        conn_local = conectar_bd() # Obtém uma nova conexão para este thread
        cursor_local = conn_local.cursor()

        global buffer_agregado

        turno_atual_id = identificar_turno(conn_local, cursor_local)

        # Usamos list() para iterar sobre uma cópia, permitindo modificações no dicionário original
        # Esta parte já força a gravação do turno anterior, se houver virada.
        for chave in list(buffer_agregado.keys()):
            id_execucao, id_maquina, id_tipo_recurso, id_ordem, id_turno_chave, id_operador = chave

            # Se o turno da chave é diferente do turno atual do sistema
            if id_turno_chave != turno_atual_id:
                logger.info(f"Virada de turno detectada para máquina {id_maquina}. Forçando gravação da produção do turno anterior.")
                forcar_gravacao_consolidada(chave, conn_local, cursor_local) # Passa a conexão local

                # Fechar o status anterior da máquina se ele estiver aberto (status 99 de virada de turno pode ser apenas para log ou visualização)
                cursor_local.execute("""
                    UPDATE TBL_StatusMaquina
                    SET DataHoraFim = GETDATE(), 
                        DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, GETDATE())
                    WHERE IDMaquina = ? AND DataHoraFim IS NULL AND Status != 99 -- Não fechar status 99
                """, (id_maquina,))
                conn_local.commit()
                logger.info(f"Status anterior da máquina {id_maquina} fechado devido à virada de turno.")

                # Opcional: Registrar um status especial de virada de turno (se TBL_StatusMaquina suporta 99)
                # Se não for um status operacional real, considere registrar em uma tabela de log de eventos internos
                # Se 99 não é um status válido, essa linha pode causar erros.
                # cursor_local.execute("""
                #     INSERT INTO TBL_StatusMaquina 
                #     (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, IDMotivoParada, DescricaoStatus)
                #     VALUES (?, 99, GETDATE(), GETDATE(), ?, 99, 'Virada de Turno')
                # """, (id_maquina, turno_atual_id))
                # conn_local.commit()
                # logger.info(f"Status 'Virada de Turno' registrado para máquina {id_maquina}.")

        with lock:
            if buffer_agregado:
                logger.info(f"🔄 Gravando {len(buffer_agregado)} registros consolidados do buffer (se existirem e não tiverem sido gravados por virada de turno) no banco...")

                # ATENÇÃO: Corrigido o acesso a 'dados'. Assume que 'dados' é o valor inteiro da quantidade.
                # Se o buffer precisar armazenar 'hora_inicial' e 'hora_final', a estrutura de 'buffer_agregado'
                # e a forma como ele é populado precisam ser ajustadas para dicionários.
                for chave, quantidade_do_buffer in buffer_agregado.items(): # 'dados' renomeado para 'quantidade_do_buffer'
                    (
                        id_execucao, id_maquina, id_tipo_recurso,
                        id_ordem, id_turno, id_operador
                    ) = chave

                    # Usamos a quantidade diretamente do buffer.
                    # As colunas HoraInicialReal e HoraFinalReal não serão populadas por esse método de agregação.
                    # Se elas são essenciais, a forma como o buffer é populado deve ser revista.
                    data_hora_evento = datetime.now() # Data/hora da gravação da consolidação

                    try:
                        cursor_local.execute("""
                            INSERT INTO VW_EventoProducaoComCicloReal (
                                IDExecucao, IDMaquina, IDTipoRecurso, IDOrdemProducao,
                                IDTurno, IDOperador, IDTipoEvento, Quantidade,
                                TipoValor, OrigemEvento, DataHoraEvento
                                -- HoraInicialReal, HoraFinalReal -- Não populadas por este método
                            )
                            VALUES (?, ?, ?, ?, ?, ?, 1, ?, 'BOA', 'AUTOMATICO_BUFFER', ?)
                        """, (
                            id_execucao, id_maquina, id_tipo_recurso,
                            id_ordem, id_turno, id_operador, quantidade_do_buffer, # Usa a quantidade diretamente
                            data_hora_evento
                        ))
                    except Exception as e:
                        logger.error(f"❌ Erro ao gravar linha consolidada do buffer: {e}", exc_info=True)

                conn_local.commit()
                buffer_agregado.clear()
            else:
                logger.debug("Buffer de produção agregado vazio, nada para gravar.") # Adicionado para melhor rastreamento
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em gravar_buffer_agrupado: {e}", exc_info=True)
    finally:
        if conn_local:
            conn_local.close() # Fecha a conexão específica para este thread


def _update_machine_status(conn_local, cursor_local, id_maquina, new_status, id_motivo_parada=None, obs_evento='', data_hora_custom=None):
    """
    Função auxiliar para atualizar o status de uma máquina.
    VERSÃO CORRIGIDA: Aceita data_hora_custom para retroagir paradas automáticas.
    """
    # Se uma data customizada for passada (ex: do robô de inatividade), usa ela. Senão, usa AGORA.
    timestamp = data_hora_custom if data_hora_custom else datetime.now()
    
    id_turno_atual = identificar_turno(conn_local, cursor_local)
    
    new_record_id = None

    cursor_local.execute("""
        SELECT TOP 1 IDRegistroStatus, Status, IDMotivoParada
        FROM TBL_StatusMaquina 
        WHERE IDMaquina = ? AND DataHoraFim IS NULL
        ORDER BY DataHoraRegistro DESC
    """, id_maquina)
    ultimo_status_db = cursor_local.fetchone()

    # --- Lógica de atualização de status da OP ---
    if new_status == 1 and ultimo_status_db and ultimo_status_db.Status == 0:
        cursor_local.execute("SELECT IDMotivoParada FROM TBL_MotivoParada WHERE Codigo = '03'")
        motivo_setup_row = cursor_local.fetchone()
        id_motivo_setup = motivo_setup_row.IDMotivoParada if motivo_setup_row else -1

        if ultimo_status_db.IDMotivoParada == id_motivo_setup:
            logger.info(f"Máquina {id_maquina} saindo de SETUP. Iniciando atualização de status da OP.")
            cursor_local.execute("SELECT IDOrdem FROM TBL_ExecucaoOP WHERE IDMaquina = ? AND Status = 'Em Setup'", (id_maquina,))
            execucao_em_setup = cursor_local.fetchone()

            if execucao_em_setup:
                id_ordem_a_atualizar = execucao_em_setup.IDOrdem
                cursor_local.execute("UPDATE TBL_ExecucaoOP SET Status = 'Em Execucao' WHERE IDOrdem = ? AND IDMaquina = ? AND Status = 'Em Setup'", (id_ordem_a_atualizar, id_maquina))
                cursor_local.execute("SELECT IDStatus FROM TBL_StatusOrdemProducao WHERE NomeStatus = 'Em Execucao'")
                status_exec_row = cursor_local.fetchone()
                if status_exec_row:
                    cursor_local.execute("UPDATE TBL_OrdemProducao SET IDStatus = ? WHERE IDOrdem = ?", (status_exec_row.IDStatus, id_ordem_a_atualizar))
    # ---------------------------------------------

    # Evita gravar duplicado se o status for idêntico
    if ultimo_status_db and ultimo_status_db.Status == new_status:
        if (new_status == 0 and ultimo_status_db.IDMotivoParada == id_motivo_parada) or new_status == 1:
            return ultimo_status_db.IDRegistroStatus

    # Fecha o registro anterior com o timestamp correto (seja AGORA ou RETROATIVO)
    if ultimo_status_db:
        cursor_local.execute("""
            UPDATE TBL_StatusMaquina 
            SET DataHoraFim = ?, DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, ?)
            WHERE IDRegistroStatus = ?
        """, timestamp, timestamp, ultimo_status_db.IDRegistroStatus)

    # --- CORREÇÃO DA DUPLICAÇÃO DE TEXTO ---
    observacao_final = obs_evento
    if new_status == 0 and id_motivo_parada:
        try:
            cursor_local.execute("SELECT Descricao FROM TBL_MotivoParada WHERE IDMotivoParada = ?", id_motivo_parada)
            motivo_row = cursor_local.fetchone()
            if motivo_row and motivo_row.Descricao:
                # SE TIVER observação digitada, usa SÓ ELA.
                if obs_evento and obs_evento.strip():
                    observacao_final = obs_evento.strip()
                # SE NÃO TIVER observação, usa o NOME DO MOTIVO.
                else:
                    observacao_final = motivo_row.Descricao
        except Exception as e:
            logger.error(f"Erro ao buscar descrição do motivo de parada {id_motivo_parada}: {e}")
    # ----------------------------------------

    sql_insert_base = "INSERT INTO TBL_StatusMaquina ({columns}) OUTPUT INSERTED.IDRegistroStatus VALUES ({placeholders})"
    
    # IMPORTANTE: DataHoraRegistro continua sendo AGORA (log do sistema), 
    # mas DataHoraInicio usa o timestamp (que pode ser retroativo)
    data_registro_real = datetime.now()

    if new_status == 1:
        columns = "IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, ObsEvento"
        placeholders = "?, ?, ?, ?, ?, ?"
        params = (id_maquina, new_status, timestamp, data_registro_real, id_turno_atual, observacao_final)
    else:
        columns = "IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDMotivoParada, IDTurno, ObsEvento"
        placeholders = "?, ?, ?, ?, ?, ?, ?"
        id_motivo_parada_final = id_motivo_parada or ID_MOTIVO_PARADA_AUTOMATICA
        params = (id_maquina, new_status, timestamp, data_registro_real, id_motivo_parada_final, id_turno_atual, observacao_final)

    sql_insert_final = sql_insert_base.format(columns=columns, placeholders=placeholders)
    new_record_id = cursor_local.execute(sql_insert_final, params).fetchval()

    # Log do Evento
    if new_status == 1:
        cursor_local.execute("INSERT INTO TBL_EventoStatus (IDMaquina, Status, DataHoraEvento, ObsEvento) VALUES (?, ?, ?, ?)", id_maquina, new_status, timestamp, observacao_final)
    else:
        cursor_local.execute("INSERT INTO TBL_EventoStatus (IDMaquina, Status, DataHoraEvento, IDMotivoParada, ObsEvento) VALUES (?, ?, ?, ?, ?)", id_maquina, new_status, timestamp, id_motivo_parada, observacao_final)

    logger.info(f"Status da máquina {id_maquina} atualizado (Novo ID: {new_record_id}). Início efetivo: {timestamp}")
    return new_record_id
def identificar_turno(conn_thread=None, cursor_thread=None):
    """
    [VERSÃO CORRIGIDA PARA VIRADA DE TURNO v3 - 4 PARÂMETROS]
    Identifica o turno atual.
    Verifica se um turno começou HOJE ou se um turno que começou ONTEM ainda está vigente.
    """
    conexao_local_criada = False
    conn_local = conn_thread
    cursor_local = cursor_thread

    try:
        if conn_local is None or cursor_local is None:
            conn_local = conectar_bd() 
            cursor_local = conn_local.cursor()
            conexao_local_criada = True

        agora = datetime.now()
        hora_atual_time = agora.time()
        
        dia_da_semana_python = agora.weekday()
        dia_anterior_python = (agora - timedelta(days=1)).weekday()

        dias_semana_colunas = ['Seg', 'Ter', 'Qua', 'Qui', 'Sex', 'Sab', 'Dom']
        coluna_dia_atual = dias_semana_colunas[dia_da_semana_python]
        coluna_dia_anterior = dias_semana_colunas[dia_anterior_python]

        # Esta query tem 4 placeholders '?'
        query = f"""
            SELECT TOP 1 IDTurno, NomeTurno
            FROM TBL_Turno
            WHERE
                Ativo = 1
                AND (
                    -- Condição 1: Turno normal que começa e termina HOJE.
                    (
                        (Todos = 1 OR {coluna_dia_atual} = 1)
                        AND IniciaDiaAnterior = 0
                        AND ? BETWEEN CAST(HoraInicio AS TIME) AND CAST(HoraFim AS TIME) -- <--- Param 1
                    )
                    -- Condição 2: Turno que vira a noite e COMEÇA HOJE.
                    OR
                    (
                        (Todos = 1 OR {coluna_dia_atual} = 1)
                        AND IniciaDiaAnterior = 1
                        AND ? >= CAST(HoraInicio AS TIME) -- <--- Param 2
                    )
                    -- Condição 3: Turno que vira a noite e COMEÇOU ONTEM.
                    OR
                    (
                        (Todos = 1 OR {coluna_dia_anterior} = 1)
                        AND IniciaDiaAnterior = 1
                        AND ? <= CAST(HoraFim AS TIME) -- <--- Param 3
                    )
                )
            ORDER BY
                -- Prioriza turnos que estão terminando (Condição 3)
                CASE 
                    WHEN (Todos = 1 OR {coluna_dia_anterior} = 1) AND IniciaDiaAnterior = 1 AND ? <= CAST(HoraFim AS TIME) THEN 1 -- <--- Param 4
                    ELSE 2
                END,
                CAST(HoraInicio AS TIME) DESC
        """
        
        # ##### CORREÇÃO AQUI: Passando 4 parâmetros para os 4 '?' #####
        cursor_local.execute(query, (hora_atual_time, hora_atual_time, hora_atual_time, hora_atual_time))
        turno = cursor_local.fetchone()

        if turno:
            logger.debug(f"Turno atual identificado (lógica v3): {turno.IDTurno} ({turno.NomeTurno})")
            return turno.IDTurno
        else:
            logger.info(f"Nenhum turno ativo encontrado para o horário atual ({hora_atual_time})")
            return None

    except Exception as e:
        logger.error(f"Erro ao identificar turno (lógica v3): {str(e)}", exc_info=True)
        return None
    finally:
        if conexao_local_criada and conn_local:
            try:
                devolver_conexao(conn_local) 
            except Exception as e_close:
                logger.error(f"Erro ao fechar/devolver conexão criada em identificar_turno: {e_close}")
# Em planner_app.py, substitua esta função inteira:

def identificar_turno_da_maquina(conn_local, cursor_local, id_maquina):
    """
    [VERSÃO CORRIGIDA PARA VIRADA DE TURNO v3 - 5 PARÂMETROS]
    Verifica se uma MÁQUINA ESPECÍFICA está dentro de um turno agendado.
    """
    try:
        agora = datetime.now()
        hora_atual_time = agora.time()

        dia_da_semana_python = agora.weekday()
        dia_anterior_python = (agora - timedelta(days=1)).weekday()

        dias_semana_colunas = ['Seg', 'Ter', 'Qua', 'Qui', 'Sex', 'Sab', 'Dom']
        coluna_dia_atual = dias_semana_colunas[dia_da_semana_python]
        coluna_dia_anterior = dias_semana_colunas[dia_anterior_python]

        # Esta query tem 5 placeholders '?'
        query = f"""
            SELECT TOP 1 t.IDTurno
            FROM TBL_Turno t
            JOIN TBL_RecursoTurno rt ON t.IDTurno = rt.IDTurno
            WHERE rt.IDRecurso = ? -- <--- Param 1
              AND t.Ativo = 1
              AND (
                  -- Condição 1: Turno normal que começa e termina HOJE.
                  (
                      (t.Todos = 1 OR t.{coluna_dia_atual} = 1)
                      AND t.IniciaDiaAnterior = 0
                      AND ? BETWEEN CAST(t.HoraInicio AS TIME) AND CAST(t.HoraFim AS TIME) -- <--- Param 2
                  )
                  -- Condição 2: Turno que vira a noite e COMEÇA HOJE.
                  OR
                  (
                      (t.Todos = 1 OR t.{coluna_dia_atual} = 1)
                      AND t.IniciaDiaAnterior = 1
                      AND ? >= CAST(t.HoraInicio AS TIME) -- <--- Param 3
                  )
                  -- Condição 3: Turno que vira a noite e COMEÇOU ONTEM.
                  OR
                  (
                      (t.Todos = 1 OR t.{coluna_dia_anterior} = 1)
                      AND t.IniciaDiaAnterior = 1
                      AND ? <= CAST(t.HoraFim AS TIME) -- <--- Param 4
                  )
              )
             ORDER BY
                -- Prioriza turnos que estão terminando (Condição 3)
                CASE 
                    WHEN (t.Todos = 1 OR t.{coluna_dia_anterior} = 1) AND t.IniciaDiaAnterior = 1 AND ? <= CAST(t.HoraFim AS TIME) THEN 1 -- <--- Param 5
                    ELSE 2
                END,
                CAST(t.HoraInicio AS TIME) DESC
        """
        
        # ##### CORREÇÃO AQUI: Passando 5 parâmetros para os 5 '?' ####
        cursor_local.execute(query, (id_maquina, hora_atual_time, hora_atual_time, hora_atual_time, hora_atual_time))
        turno_ativo = cursor_local.fetchone()

        return turno_ativo.IDTurno if turno_ativo else None
    except Exception as e:
        logger.error(f"Erro ao identificar turno para a máquina {id_maquina} (lógica v3): {e}", exc_info=True)
        return None

# Decoradores
def login_requerido(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'usuario_id' not in session:
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function
    
# Em planner_app.py, substitua o decorador

def permissao_requerida(rota):
    def decorator(f):
        @wraps(f)
        def decorated_function(*args, **kwargs):
            if 'usuario_id' not in session:
                return redirect(url_for('login'))
            id_grupo_usuario = session.get('usuario_grupo')
            if id_grupo_usuario == 1:
                return f(*args, **kwargs)
            conn_local = None
            try:
                conn_local = obter_conexao()
                cursor_local = conn_local.cursor()
                # Query correta com JOIN
                cursor_local.execute("""
                    SELECT 1
                    FROM TBL_PermissaoGrupo pg
                    JOIN TBL_permissao p ON pg.IDPermissao = p.IDPermissao
                    WHERE pg.IDGrupo = ? AND p.Rota = ?
                """, (id_grupo_usuario, rota))
                if cursor_local.fetchone():
                    return f(*args, **kwargs)
                else:
                    flash("Acesso negado.", "error")
                    return redirect(url_for('home'))
            except Exception as e:
                logger.error(f"Erro no decorador de permissão: {e}", exc_info=True)
                flash("Ocorreu um erro ao verificar suas permissões.", "error")
                return redirect(url_for('home'))
            finally:
                if conn_local:
                    devolver_conexao(conn_local)
        return decorated_function
    return decorator

def somente_admin(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        id_admin = 1  
        if session.get('usuario_grupo') != id_admin:
            flash("Acesso restrito ao administrador.", "error")
            return redirect(url_for('home')) # Redireciona para home ou outra página
        return f(*args, **kwargs)
    return decorated_function
    
@app.before_request
def before_request_func():
    """
    Função executada antes de cada requisição.
    Inicializa o pool de conexões e tenta definir o turno inicial do sistema.
    """
    global last_known_system_turn_id
    if not hasattr(app, 'pool_initialized'):
        inicializar_pool()
        # app.pool_initialized = True # Já setado dentro de inicializar_pool()
        if last_known_system_turn_id is None:
            # obter_turno_atual já gerencia sua própria conexão
            last_known_system_turn_id = identificar_turno() 
            logger.info(f"Turno inicial do sistema definido como: {last_known_system_turn_id}")
            if last_known_system_turn_id is None:
                logger.warning("Não foi possível identificar um turno inicial para o sistema.")
                

# Função auxiliar para buscar configurações (pode colocar no topo do arquivo)
def obter_configuracao(chave, conn_local, cursor_local):
    try:
        cursor_local.execute("SELECT ValorConfig FROM TBL_Configuracao WHERE ChaveConfig = ?", chave)
        resultado = cursor_local.fetchone()
        return resultado.ValorConfig if resultado else None
    except Exception as e:
        logger.error(f"Erro ao obter configuração para a chave '{chave}': {e}")
        return None
# Coloque esta função em seu arquivo planner_app.py, junto com as outras funções de banco de dados.
# Lembre-se de importar o pandas no topo do seu arquivo, se ainda não o fez:
# import pandas as pd

def buscar_relatorio_oee_diario():
    """
    Busca os dados de OEE diário consolidados por máquina no banco de dados.
    Utiliza o pool de conexões existente na aplicação.
    Retorna um DataFrame do Pandas com os resultados.
    """
    conn_local = None
    logger.info("Iniciando busca do relatório de OEE diário...")

    # Esta é a consulta SQL que criamos e corrigimos anteriormente.
    # Ela calcula o OEE médio do dia atual (desde a meia-noite até agora).
    query_oee = """
    SELECT
        r.NomeMaquina,
        CAST(AVG(oee.Disponibilidade) * 100 AS DECIMAL(5, 2)) AS Disponibilidade,
        CAST(AVG(oee.Performance) * 100 AS DECIMAL(5, 2)) AS Performance,
        CAST(AVG(oee.Qualidade) * 100 AS DECIMAL(5, 2)) AS Qualidade,
        CAST(AVG(oee.OEE) * 100 AS DECIMAL(5, 2)) AS OEE
    FROM
        [pln_edu].[dbo].[TBL_IndiceOEE] AS oee
    INNER JOIN
        [pln_edu].[dbo].[TBL_ExecucaoOP] AS e ON oee.IDExecucao = e.IDExecucao
    INNER JOIN
        [pln_edu].[dbo].[TBL_Recurso] AS r ON e.IDMaquina = r.IDMaquina
    WHERE
        -- Filtra os registros do dia atual
        CAST(oee.DataHoraCalculo AS DATE) = CAST(GETDATE() AS DATE)
    GROUP BY
        r.NomeMaquina
    ORDER BY
        r.NomeMaquina;
    """

    try:
        # Usa o seu sistema de pool de conexões para obter uma conexão
        conn_local = obter_conexao()
        
        # O Pandas e o pyodbc cuidam do cursor e da busca dos dados
        df_relatorio = pd.read_sql_query(query_oee, conn_local)
        
        logger.info(f"Relatório de OEE encontrado com {len(df_relatorio)} máquinas.")
        return df_relatorio

    except Exception as e:
        logger.error(f"Erro ao buscar relatório de OEE diário: {e}", exc_info=True)
        # Retorna um DataFrame vazio em caso de falha para não quebrar o resto do código
        return pd.DataFrame()
    finally:
        # Devolve a conexão ao pool ao final da operação
        if conn_local:
            devolver_conexao(conn_local)
def calcular_e_salvar_oee_periodicamente():
    """
    [VERSÃO ATUALIZADA] Calcula o OEE para TODAS as máquinas ativas que estão em um turno,
    vinculando o cálculo ao IDOrdem que está em execução no momento.
    """
    conn_local = None
    logger.info("Iniciando cálculo periódico de OEE (Vinculado à Ordem)...")
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("SELECT IDMaquina FROM TBL_Recurso WHERE Ativo = 1")
        todas_maquinas_ativas = cursor_local.fetchall()

        if not todas_maquinas_ativas:
            logger.debug("Nenhuma máquina ativa encontrada para cálculo de OEE.")
            return

        for maquina_row in todas_maquinas_ativas:
            id_maquina = maquina_row.IDMaquina
            # Variáveis para armazenar contexto da ordem
            id_execucao_contexto = None
            id_ordem_contexto = None # <<< NOVO
            id_ordem_operacao_contexto = None # <<< NOVO (Opcional, mas bom ter)

            try:
                # Garante transação limpa para cada máquina
                # conn_local.commit() # Removido - Commit/Rollback é melhor no final do loop da máquina ou no bloco finally geral

                id_turno_atual = identificar_turno_da_maquina(conn_local, cursor_local, id_maquina)
                if not id_turno_atual:
                    # logger.debug(f"Máquina {id_maquina} fora de turno, pulando cálculo OEE.") # Log opcional
                    continue # Pula para a próxima máquina se esta não estiver em turno

                # --- ALTERAÇÃO AQUI: Busca IDExecucao, IDOrdem e IDOrdemOperacao ---
                cursor_local.execute("""
                    SELECT TOP 1
                        E.IDExecucao, E.IDOrdem, E.IDOrdemOperacao, -- <<< ADICIONADO IDOrdem e IDOrdemOperacao
                        P.IDProduto, O.UsarTempoCicloRecurso,
                        CASE
                            WHEN O.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.TempoCicloPadraoSegundos
                            ELSE P.TempoCicloSegundos
                        END AS TempoCicloFinal,
                        CASE
                            WHEN O.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.FatorMultiplicacao
                            ELSE P.FatorMultiplicacao
                        END AS FatorMultiplicacaoFinal
                    FROM TBL_ExecucaoOP E WITH (NOLOCK)
                    JOIN TBL_OrdemProducao O WITH (NOLOCK) ON O.IDOrdem = E.IDOrdem
                    JOIN TBL_Produto P WITH (NOLOCK) ON P.IDProduto = O.IDProduto
                    LEFT JOIN TBL_RecursoProduto RP WITH (NOLOCK) ON E.IDMaquina = RP.IDRecurso AND O.IDProduto = RP.IDProduto
                    WHERE E.IDMaquina = ? AND E.Status IN ('Em Execucao', 'Em Setup') -- Considera Setup também para ter contexto
                    ORDER BY E.DataHoraInicio DESC
                """, id_maquina)
                row_ordem_ativa = cursor_local.fetchone()
                # --- FIM DA ALTERAÇÃO ---

                if row_ordem_ativa:
                    id_execucao_contexto = row_ordem_ativa.IDExecucao
                    id_ordem_contexto = row_ordem_ativa.IDOrdem # <<< CAPTURA O IDOrdem
                    id_ordem_operacao_contexto = row_ordem_ativa.IDOrdemOperacao # <<< CAPTURA O IDOrdemOperacao
                    tempo_ciclo_seg = float(row_ordem_ativa.TempoCicloFinal or 0)
                    fator_multiplicacao = float(row_ordem_ativa.FatorMultiplicacaoFinal or 1)
                else:
                    # logger.debug(f"Nenhuma ordem ativa encontrada para máquina {id_maquina}, pulando cálculo OEE.") # Log opcional
                    continue # Se não tem ordem ativa, não calcula OEE (ou pode calcular OEE da máquina sem vincular à ordem)

                # --- Lógica de cálculo de Disponibilidade, Qualidade, Performance (EXISTENTE) ---
                # (O cálculo em si não muda, apenas garantimos o contexto da ordem)
                disponibilidade_dict = obter_disponibilidade_turno(id_maquina, id_turno_atual)
                disponibilidade_val = float(disponibilidade_dict.get('Disponibilidade_Pct', 0)) / 100.0
                tempo_rodando_seg_turno = disponibilidade_dict.get('TempoRodando', 0)

                cursor_local.execute("SELECT HoraInicio, HoraFim FROM TBL_Turno WHERE IDTurno = ?", id_turno_atual)
                row_turno = cursor_local.fetchone()
                hoje = datetime.now().date()
                inicio_turno_dt = datetime.combine(hoje, row_turno.HoraInicio)
                if row_turno.HoraFim < row_turno.HoraInicio and datetime.now().time() < row_turno.HoraInicio:
                    inicio_turno_dt = inicio_turno_dt - timedelta(days=1)

                # Busca produção BOA e REFUGO DO TURNO ATUAL PARA A MÁQUINA
                cursor_local.execute("""
                    SELECT SUM(CASE WHEN TipoValor IN ('BOA', 'ESTORNO') THEN Quantidade ELSE 0 END) as QtdBoaTurno,
                           SUM(CASE WHEN TipoValor = 'REFUGO' THEN Quantidade ELSE 0 END) as QtdRefugoTurno
                    FROM VW_EventoProducaoComCicloReal WITH (NOLOCK)
                    WHERE IDMaquina = ? AND IDTurno = ? AND DataHoraEvento >= ?
                """, (id_maquina, id_turno_atual, inicio_turno_dt)) # <<< REMOVIDO o id_ordem_contexto

                producao_no_turno = cursor_local.fetchone()
                qtd_boa_turno = float(producao_no_turno.QtdBoaTurno or 0) if producao_no_turno else 0.0
                qtd_refugo_turno = float(producao_no_turno.QtdRefugoTurno or 0) if producao_no_turno else 0.0
                producao_total_turno = qtd_boa_turno + qtd_refugo_turno

                qualidade_val = (qtd_boa_turno / producao_total_turno) if producao_total_turno > 0 else 1.0 # Qualidade = 1 se não produziu nada
                performance_val = 0.0

                if tempo_rodando_seg_turno > 0 and producao_total_turno > 0 and tempo_ciclo_seg > 0 and fator_multiplicacao > 0:
                    tempo_teorico_seg_turno = (producao_total_turno * tempo_ciclo_seg) / fator_multiplicacao
                    performance_val = tempo_teorico_seg_turno / tempo_rodando_seg_turno
                elif tempo_rodando_seg_turno > 0: # Se rodou mas não produziu, performance é 0
                     performance_val = 0.0
                # Se não rodou (tempo_rodando_seg_turno == 0), performance_val continua 0 como inicializado

                # Garante que performance não exceda um limite razoável (ex: 150%) para evitar distorções
                performance_val = min(performance_val, 1.5)

                oee_final = disponibilidade_val * performance_val * qualidade_val

                # --- ALTERAÇÃO AQUI: Adiciona IDOrdem (e IDOrdemOperacao se existir) ao INSERT ---
                cursor_local.execute("""
                    INSERT INTO TBL_IndiceOEE
                    (IDExecucao, IDMaquina, IDTurno, IDOrdem, IDOrdemOperacao, -- <<< NOVAS COLUNAS
                     Disponibilidade, Performance, Qualidade, OEE, DataHoraCalculo)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, GETDATE()) -- <<< NOVOS PLACEHOLDERS
                """, (id_execucao_contexto, id_maquina, id_turno_atual,
                      id_ordem_contexto, id_ordem_operacao_contexto, # <<< NOVOS VALORES
                      disponibilidade_val, performance_val, qualidade_val, oee_final))
                # --- FIM DA ALTERAÇÃO ---

                conn_local.commit() # Commit por máquina após cálculo bem-sucedido
                logger.info(f"Snapshot OEE salvo: Máq={id_maquina}, Turno={id_turno_atual}, Ordem={id_ordem_contexto}, OEE={oee_final:.2%}")

            except Exception as e_maq:
                if conn_local: conn_local.rollback() # Rollback SE der erro nesta máquina específica
                logger.error(f"Falha ao calcular OEE para a máquina {id_maquina}: {e_maq}", exc_info=True)
                # Continua para a próxima máquina

    except Exception as e_geral:
        # Não faz rollback aqui, pois pode ter feito commits parciais
        logger.error(f"ERRO GERAL no processo de cálculo periódico de OEE: {e_geral}", exc_info=True)
    finally:
        if conn_local:
            devolver_conexao(conn_local)

def enviar_relatorio_oee_diario():
     """
     Busca os dados do ÚLTIMO OEE de cada máquina ativa, formata os valores
     e envia por e-mail para os grupos marcados.
     """
     conn_local = None
     logger.info("INICIANDO GERAÇÃO E ENVIO DO RESUMO DIÁRIO DE KPI (LÓGICA ATUALIZADA)...")
     try:
         conn_local = obter_conexao()
         cursor_local = conn_local.cursor()
        
         # --- INÍCIO DA QUERY CORRIGIDA ---
         # Esta query agora busca o último registro de OEE para cada máquina ativa no dia de hoje.
         query_oee = """
             WITH UltimoOEE_PorMaquina AS (
                 SELECT
                     r.NomeMaquina,
                     oee.Disponibilidade,
                     oee.Performance,
                     oee.Qualidade,
                     oee.OEE,
                     ROW_NUMBER() OVER(PARTITION BY oee.IDMaquina ORDER BY oee.DataHoraCalculo DESC) as rn
                 FROM TBL_IndiceOEE AS oee
                 JOIN TBL_Recurso AS r ON oee.IDMaquina = r.IDMaquina
                 WHERE
                     CAST(oee.DataHoraCalculo AS DATE) = CAST(GETDATE() AS DATE)
                     AND oee.IDMaquina IS NOT NULL
             )
             SELECT
                 NomeMaquina,
                 CAST(Disponibilidade * 100 AS DECIMAL(5, 2)) AS Disponibilidade,
                 CAST(Performance * 100 AS DECIMAL(5, 2)) AS Performance,
                 CAST(Qualidade * 100 AS DECIMAL(5, 2)) AS Qualidade,
                 CAST(OEE * 100 AS DECIMAL(5, 2)) AS OEE
             FROM UltimoOEE_PorMaquina
             WHERE rn = 1
             ORDER BY NomeMaquina;
         """
#         # --- FIM DA QUERY CORRIGIDA ---

         df_relatorio = pd.read_sql_query(query_oee, conn_local)

         if df_relatorio.empty:
             logger.info("Nenhum dado de KPI (últimos registros) encontrado para o dia de hoje. Relatório não será enviado.")
             return

#         # A formatação para porcentagem continua a mesma
         colunas_para_formatar = ['Disponibilidade', 'Performance', 'Qualidade', 'OEE']
         for coluna in colunas_para_formatar:
             df_relatorio[coluna] = df_relatorio[coluna].apply(lambda x: f"{int(round(float(x), 0))}%")

         # O resto da função para buscar destinatários e enviar o e-mail permanece igual.
         cursor_local.execute("""
             SELECT DISTINCT U.Email
             FROM TBL_Usuario U
             JOIN TBL_GrupoUsuario G ON U.IDGrupo = G.IDGrupo
             WHERE G.RecebeRelatorioOEE = 1 AND U.Ativo = 1 AND U.Email IS NOT NULL AND U.Email <> ''
         """)
         destinatarios = [row.Email for row in cursor_local.fetchall()]
        
         if not destinatarios:
             logger.warning("Nenhum usuário encontrado nos grupos marcados para receber o relatório de KPI. E-mail não será enviado.")
             return
            
         config_keys = "('SMTP_HOST', 'SMTP_PORT', 'SMTP_USER', 'SMTP_PASSWORD', 'SMTP_USE_TLS', 'SMTP_SENDER_EMAIL', 'SMTP_SENDER_NAME')"
         cursor_local.execute(f"SELECT ChaveConfig, ValorConfig FROM TBL_Configuracao WHERE ChaveConfig IN {config_keys}")
         config_raw = cursor_local.fetchall()
         config = {row.ChaveConfig: row.ValorConfig for row in config_raw}

         data_hoje = datetime.now().strftime('%d/%m/%Y')
         assunto = f"Resumo Diário KPI - {data_hoje}"
         html_body = f"""
         <html>
             <head>
                 <style>
                     body {{ font-family: Arial, sans-serif; }}
                     table {{ border-collapse: collapse; width: 90%; margin: 20px auto; }}
                     th, td {{ border: 1px solid #cccccc; text-align: center; padding: 10px; }}
                     th {{ background-color: #004a99; color: white; }}
                     tr:nth-child(even) {{ background-color: #f2f2f2; }}
                     h2 {{ color: #004a99; text-align: center; }}
                 </style>
             </head>
             <body>
                 <h2>Resumo Diário de KPIs do Dia {data_hoje}</h2>
                 <p style="font-size: 0.9em; text-align: center; color: #555;">Os valores abaixo representam o último índice de OEE registrado para cada máquina hoje.</p>
                 {df_relatorio.to_html(index=False, border=0)}
                 <p style="font-size: 0.8em; text-align: center; color: #777;">Este é um e-mail automático gerado pelo Sistema Planner.</p>
             </body>
         </html>
         """
         msg = MIMEMultipart()
        
         sender_name = config.get('SMTP_SENDER_NAME', 'Planner')
         sender_email = config.get('SMTP_SENDER_EMAIL')
         msg['From'] = formataddr((sender_name, sender_email))
        
         msg['To'] = ", ".join(destinatarios)
         msg['Subject'] = assunto
         msg.attach(MIMEText(html_body, 'html'))
        
         server = smtplib.SMTP(config.get('SMTP_HOST'), int(config.get('SMTP_PORT')))
         if config.get('SMTP_USE_TLS', 'false').lower() == 'true':
             server.starttls()
         server.login(config.get('SMTP_USER'), config.get('SMTP_PASSWORD'))
         server.sendmail(config.get('SMTP_SENDER_EMAIL'), destinatarios, msg.as_string())
         server.quit()
        
         logger.info(f"E-mail de resumo de KPI (lógica atualizada) enviado com sucesso para {len(destinatarios)} destinatário(s).")

     except Exception as e:
         logger.error(f"ERRO ao gerar/enviar resumo diário de KPI: {e}", exc_info=True)
     finally:
         if conn_local:
             devolver_conexao(conn_local)



def verificar_e_corrigir_estouro_setup(id_maquina, id_registro_status_setup):
    """
    Esta função é EXECUTADA PELO AGENDADOR no momento em que o setup deveria terminar.
    Ela verifica se a máquina ainda está em setup e, se estiver, troca o motivo da parada.
    """
    conn_local = None
    logger.info(f"[JOB AGENDADO] Verificando estouro de setup para máquina {id_maquina}, registro {id_registro_status_setup}.")
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # 1. Verifica se o registro de setup ainda está aberto
        cursor_local.execute(
            "SELECT DataHoraFim FROM TBL_StatusMaquina WHERE IDRegistroStatus = ?",
            id_registro_status_setup
        )
        registro_setup = cursor_local.fetchone()

        # 2. Se DataHoraFim NÃO for nulo, significa que a produção já começou. O trabalho termina aqui.
        if not registro_setup or registro_setup.DataHoraFim is not None:
            logger.info(f"[JOB AGENDADO] Setup para o registro {id_registro_status_setup} já foi finalizado. Nenhuma ação necessária.")
            return

        # 3. Se ainda está aberto, o setup ESTOUROU.
        logger.warning(f"[JOB AGENDADO] ESTOURO DE SETUP DETECTADO para máquina {id_maquina}!")
        
        # 4. Pega o ID do motivo de parada "Estouro de Setup"
        cursor_local.execute("SELECT IDMotivoParada FROM TBL_MotivoParada WHERE Codigo = '03'")
        motivo_estouro = cursor_local.fetchone()
        if not motivo_estouro:
            logger.error("[JOB AGENDADO] Motivo de parada 'SETUP_OVER' não encontrado! Não foi possível reclassificar a parada.")
            return
        
        id_motivo_estouro_setup = motivo_estouro.IDMotivoParada

        # 5. Usa a função _update_machine_status para trocar a parada de "Setup" para "Estouro de Setup"
        _update_machine_status(
            conn_local, cursor_local, id_maquina, 0,
            id_motivo_parada=id_motivo_estouro_setup,
            obs_evento='Setup planejado excedido'
        )
        
        conn_local.commit()
        logger.info(f"[JOB AGENDADO] Parada da máquina {id_maquina} reclassificada para 'Estouro de Setup'.")

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"[JOB AGENDADO] Erro CRÍTICO ao verificar estouro de setup: {e}", exc_info=True)
    finally:
        if conn_local: devolver_conexao(conn_local)


def agendar_verificacao_estouro_setup(id_maquina, id_registro_status_setup, tempo_setup_segundos):
    """
    Agenda um job para ser executado uma única vez, exatamente após o fim do tempo de setup.
    """
    if tempo_setup_segundos <= 0:
        return

    data_execucao = datetime.now() + timedelta(seconds=tempo_setup_segundos)
    job_id = f"verificacao_setup_maq_{id_maquina}_reg_{id_registro_status_setup}"
    
    # Usa o objeto 'scheduler' importado para adicionar o trabalho
    scheduler.add_job(
        verificar_e_corrigir_estouro_setup,
        trigger='date',
        run_date=data_execucao,
        args=[id_maquina, id_registro_status_setup],
        id=job_id,
        replace_existing=True # Garante que não haja jobs duplicados para o mesmo evento
    )
    logger.info(f"Job '{job_id}' agendado para {data_execucao.strftime('%Y-%m-%d %H:%M:%S')} para verificar estouro de setup.")
            

@app.route('/configuracoes', methods=['GET', 'POST'])
@login_requerido
@somente_admin
def configuracoes():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            # Log para debug: ver o que está chegando do formulário
            logger.info(f"Dados recebidos no formulário de configurações: {request.form}")

            # O dicionário que prepara os dados para salvar
            configs_para_salvar = {
                'BASE_URL': request.form.get('base_url'),
                'SMTP_HOST': request.form.get('smtp_host'),
                'SMTP_PORT': request.form.get('smtp_port'),
                'SMTP_USER': request.form.get('smtp_user'),
                'SMTP_SENDER_NAME': request.form.get('smtp_sender_name'),
                'SMTP_SENDER_EMAIL': request.form.get('smtp_sender_email'),
                'SMTP_USE_TLS': 'true' if 'smtp_use_tls' in request.form else 'false',
                'OEE_REPORT_SCHEDULE_TIME': request.form.get('oee_report_schedule_time'),
                'USA_UNIDADES_POR_CAIXA': 'true' if 'usa_unidades_caixa' in request.form else 'false',
                'USA_CAMPO_DESCRICAO_PRODUTO': 'true' if 'usa_campo_descricao' in request.form else 'false',
                'CAMINHO_BASE_DOCUMENTOS': request.form.get('caminho_base_documentos'),
                'CAMINHO_BASE_DOCUMENTOS_OPERACAO': request.form.get('caminho_base_documentos_operacao'),
                'PERMITE_AJUSTE_ESTOQUE_MANUAL': 'true' if 'permite_ajuste_estoque_manual' in request.form else 'false',
                'USA_UNIDADE_PADRAO_MP': 'true' if 'usa_unidade_padrao_mp' in request.form else 'false',
                'TEMPO_MAXIMO_CLASSIFICACAO_PARADA_MIN': request.form.get('tempo_max_classificacao')
            }

            # Query SQL Robust (MERGE) - Funciona como um "Upsert"
            sql_merge = """
                MERGE TBL_Configuracao AS target
                USING (SELECT ? AS Chave, ? AS Valor) AS source
                ON (target.ChaveConfig = source.Chave)
                WHEN MATCHED THEN
                    UPDATE SET ValorConfig = source.Valor, DataAtualizacao = GETDATE()
                WHEN NOT MATCHED THEN
                    INSERT (ChaveConfig, ValorConfig, DataAtualizacao)
                    VALUES (source.Chave, source.Valor, GETDATE());
            """

            for chave, valor in configs_para_salvar.items():
                if valor is not None: 
                    # Executa o MERGE para cada configuração
                    cursor_local.execute(sql_merge, (chave, str(valor)))

            # Lógica para a senha (separada por segurança)
            smtp_password = request.form.get('smtp_password')
            if smtp_password and smtp_password.strip(): # Só salva se não estiver vazio
                cursor_local.execute(sql_merge, ('SMTP_PASSWORD', smtp_password))

            conn_local.commit()
            
            # Recarrega agendamentos (se necessário)
            try:
                from scheduler import recarregar_agendamentos
                recarregar_agendamentos()
                
                # ### <<< ADICIONADO AQUI: Garante que o OEE volta a rodar após o reload >>> ###
                garantir_agendamento_oee() 
                # ############################################################################

            except ImportError:
                logger.warning("Módulo scheduler não encontrado ou erro ao recarregar.")

            flash("Configurações salvas com sucesso!", "success")
            return redirect(url_for('configuracoes'))

        # --- LÓGICA GET ---
        chaves_necessarias = [
            'BASE_URL',
            'SMTP_HOST', 'SMTP_PORT', 'SMTP_USER', 'SMTP_SENDER_NAME', 
            'SMTP_SENDER_EMAIL', 'SMTP_USE_TLS', 'OEE_REPORT_SCHEDULE_TIME',
            'USA_UNIDADES_POR_CAIXA', 'USA_CAMPO_DESCRICAO_PRODUTO',
            'CAMINHO_BASE_DOCUMENTOS', 'CAMINHO_BASE_DOCUMENTOS_OPERACAO',
            'PERMITE_AJUSTE_ESTOQUE_MANUAL', 'USA_UNIDADE_PADRAO_MP',
            'TEMPO_MAXIMO_CLASSIFICACAO_PARADA_MIN'
        ]
        
        configs = {}
        # Busca todas as configs de uma vez para ser mais rápido
        cursor_local.execute(f"SELECT ChaveConfig, ValorConfig FROM TBL_Configuracao WHERE ChaveConfig IN ({','.join(['?']*len(chaves_necessarias))})", chaves_necessarias)
        rows = cursor_local.fetchall()
        
        # Converte para dicionário
        db_configs = {row.ChaveConfig: row.ValorConfig for row in rows}
        
        # Garante que todas as chaves existam no dicionário final, mesmo que nulas no banco
        for chave in chaves_necessarias:
            configs[chave] = db_configs.get(chave, '')

        return render_template('configuracoes.html', configs=configs)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro CRÍTICO em /configuracoes: {e}", exc_info=True)
        flash(f"Erro ao salvar configurações: {str(e)}", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

def formatar_segundos_para_hms(segundos):
    """Converte uma quantidade total de segundos para uma string no formato HH:MM:SS."""
    if segundos is None:
        return "00:00:00"
    segundos = int(segundos)
    horas, resto = divmod(segundos, 3600)
    minutos, segundos_finais = divmod(resto, 60)
    return f"{horas:02d}:{minutos:02d}:{segundos_finais:02d}"
    
# Em planner_app.py, substitua a função de login inteira por esta:

@app.route('/login', methods=['GET', 'POST'])
def login():
    conn_local = None
    try:
        if request.method == 'POST':
            codigo = request.form['codigo']
            senha = request.form['senha']

            conn_local = obter_conexao()
            cursor_local = conn_local.cursor()

            # 1. Busca o usuário pelo código de acesso
            cursor_local.execute("""
                SELECT U.IDUsuario, U.NomeUsuario, U.IDGrupo, G.NomeGrupo, U.Senha
                FROM TBL_Usuario U
                JOIN TBL_GrupoUsuario G ON U.IDGrupo = G.IDGrupo
                WHERE U.CodigoUsuario = ? AND U.Ativo = 1
            """, (codigo,))
            usuario = cursor_local.fetchone()

            # 2. Verifica se o usuário foi encontrado E se a senha corresponde
            if usuario and check_password_hash(usuario.Senha, senha):
                # Se a senha estiver correta, inicia a sessão
                session['usuario_id'] = usuario.IDUsuario
                session['usuario_nome'] = usuario.NomeUsuario
                session['grupo'] = usuario.NomeGrupo
                session['usuario_grupo'] = usuario.IDGrupo
                
                cursor_local.execute("""
                    SELECT p.Rota
                    FROM TBL_PermissaoGrupo pg
                    JOIN TBL_permissao p ON pg.IDPermissao = p.IDPermissao
                    WHERE pg.IDGrupo = ?
                """, (usuario.IDGrupo,))
                
                permissoes = [row.Rota for row in cursor_local.fetchall()]
                session['permissao'] = permissoes

                # --- INÍCIO DA CORREÇÃO ---
                # Verifica o nome do grupo do usuário na sessão que acabamos de criar.
                # IMPORTANTE: O nome do grupo deve ser EXATAMENTE 'Operador'.
                if session.get('grupo') == 'Operadores':
                    # Se for do grupo 'Operador', redireciona direto para o dashboard.
                    return redirect(url_for('dashboard'))
                else:
                    # Para todos os outros grupos, redireciona para a página home.
                    return redirect(url_for('home'))
                # --- FIM DA CORREÇÃO ---

            else:
                # Se o usuário não existe ou a senha está incorreta, mostra o erro
                flash('Credenciais inválidas', 'error')
                return render_template('login.html', erro='Credenciais inválidas')

        return render_template('login.html')
    except Exception as e:
        logger.error(f"Erro no login: {e}", exc_info=True)
        flash('Ocorreu um erro ao tentar fazer login. Tente novamente.', 'error')
        return render_template('login.html', erro='Erro interno')
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/logout')
def logout():
    session.clear()
    flash("Você foi desconectado.", "info")
    return redirect(url_for('login'))
    
@app.route('/recuperar_senha', methods=['GET', 'POST'])
def recuperar_senha():
    conn_local = None
    if request.method == 'POST':
        email = request.form.get('email')
        try:
            conn_local = obter_conexao()
            cursor_local = conn_local.cursor()
            cursor_local.execute("SELECT IDUsuario FROM TBL_Usuario WHERE Email = ? AND Ativo = 1", (email,))
            user = cursor_local.fetchone()

            if user:
                # --- INÍCIO DA ALTERAÇÃO ---
                
                # 1. Busca a URL base do banco de dados
                base_url = obter_configuracao('BASE_URL', conn_local, cursor_local)
                if not base_url:
                    # Se não estiver configurada, usa um fallback e avisa no log
                    logger.error("A 'BASE_URL' não está definida nas configurações. O link de e-mail pode não funcionar externamente.")
                    # Como fallback, ele vai gerar um link relativo ao servidor onde a requisição foi feita
                    link = url_for('resetar_senha', token=s.dumps(email, salt='password-reset-salt'), _external=True)
                else:
                    # 2. Gera a parte final do link (relativa)
                    token = s.dumps(email, salt='password-reset-salt')
                    path_do_link = url_for('resetar_senha', token=token)
                    # 3. Junta a URL base com a parte final para criar o link completo
                    link = f"{base_url.rstrip('/')}{path_do_link}"

                # --- FIM DA ALTERAÇÃO ---

                # Enviar o e-mail
                enviar_email_reset(email, link)

            flash('Se um usuário com este e-mail existir, um link para redefinição de senha foi enviado.', 'success')
            return redirect(url_for('recuperar_senha'))

        except Exception as e:
            logger.error(f"Erro em /recuperar_senha: {e}", exc_info=True)
            flash("Ocorreu um erro ao processar sua solicitação.", "error")
        finally:
            if conn_local:
                devolver_conexao(conn_local)

    return render_template('recuperar_senha.html')
def enviar_email_reset(destinatario, link_reset):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # Busca as configurações de SMTP do banco
        config_keys = "('SMTP_HOST', 'SMTP_PORT', 'SMTP_USER', 'SMTP_PASSWORD', 'SMTP_USE_TLS', 'SMTP_SENDER_EMAIL', 'SMTP_SENDER_NAME')"
        cursor_local.execute(f"SELECT ChaveConfig, ValorConfig FROM TBL_Configuracao WHERE ChaveConfig IN {config_keys}")
        config_raw = cursor_local.fetchall()
        config = {row.ChaveConfig: row.ValorConfig for row in config_raw}
        
        assunto = "Redefinição de Senha - Sistema Planner"
        html_body = f"""
        <html>
            <body>
                <h2>Redefinição de Senha</h2>
                <p>Olá,</p>
                <p>Você solicitou a redefinição da sua senha no Sistema Planner. Por favor, clique no link abaixo para criar uma nova senha:</p>
                <p><a href="{link_reset}">Redefinir Minha Senha</a></p>
                <p>Este link é válido por 1 hora. Se você não solicitou esta alteração, por favor ignore este e-mail.</p>
                <br>
                <p>Atenciosamente,<br>Equipe Planner</p>
            </body>
        </html>
        """
        
        msg = MIMEMultipart()
        sender_name = config.get('SMTP_SENDER_NAME', 'Planner')
        sender_email = config.get('SMTP_SENDER_EMAIL')
        msg['From'] = formataddr((sender_name, sender_email))
        msg['To'] = destinatario
        msg['Subject'] = assunto
        msg.attach(MIMEText(html_body, 'html'))
        
        server = smtplib.SMTP(config.get('SMTP_HOST'), int(config.get('SMTP_PORT')))
        if config.get('SMTP_USE_TLS', 'false').lower() == 'true':
            server.starttls()
        server.login(config.get('SMTP_USER'), config.get('SMTP_PASSWORD'))
        server.sendmail(sender_email, [destinatario], msg.as_string())
        server.quit()
        
        logger.info(f"E-mail de redefinição de senha enviado para {destinatario}.")

    except Exception as e:
        logger.error(f"ERRO ao enviar e-mail de redefinição de senha: {e}", exc_info=True)
        # É importante não travar a aplicação se o e-mail falhar, o log já é suficiente.
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/resetar_senha/<token>', methods=['GET', 'POST'])
def resetar_senha(token):
    try:
        # Tenta validar o token, com tempo de expiração de 3600s (1 hora)
        email = s.loads(token, salt='password-reset-salt', max_age=3600)
    except:
        flash('O link para redefinição de senha é inválido ou expirou.', 'error')
        return redirect(url_for('recuperar_senha'))

    if request.method == 'POST':
        senha = request.form['senha']
        confirmar_senha = request.form['confirmar_senha']

        if not senha or senha != confirmar_senha:
            flash('As senhas não coincidem ou estão em branco.', 'error')
            return render_template('resetar_senha.html')

        conn_local = None
        try:
            conn_local = obter_conexao()
            cursor_local = conn_local.cursor()
            
            # Gera o hash da nova senha
            senha_hash = generate_password_hash(senha)
            
            # Atualiza a senha no banco de dados
            cursor_local.execute("UPDATE TBL_Usuario SET Senha = ? WHERE Email = ?", (senha_hash, email))
            conn_local.commit()

            flash('Sua senha foi redefinida com sucesso! Você já pode fazer login.', 'success')
            return redirect(url_for('login'))
        except Exception as e:
            if conn_local: conn_local.rollback()
            logger.error(f"Erro ao salvar nova senha: {e}", exc_info=True)
            flash('Ocorreu um erro ao salvar sua nova senha.', 'error')
        finally:
            if conn_local:
                devolver_conexao(conn_local)

    return render_template('resetar_senha.html')            
            
@app.route('/home')
@login_requerido
def home():
    conn_local = None
    # Define valores padrão para todos os KPIs
    producao_hoje = 0
    total_alertas = 0
    oee_final = 0
    total_maquinas_ativas = 0
    
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # 1. Total de Máquinas Ativas
        cursor_local.execute("SELECT COUNT(*) FROM TBL_Recurso WHERE Ativo = 1")
        total_maquinas_ativas_row = cursor_local.fetchone()
        if total_maquinas_ativas_row:
            total_maquinas_ativas = total_maquinas_ativas_row[0]

        # --- INÍCIO DA ALTERAÇÃO (V4 - ROBUSTA COM CONVERT) ---
        # 2. Produção Total do "Dia de Produção" (baseado nos turnos)
        query_producao_debug_v4 = """
            DECLARE @Hoje DATE = CAST(GETDATE() AS DATE);
            DECLARE @Amanha DATE = DATEADD(day, 1, @Hoje);
            
            DECLARE @InicioDiaProd TIME;
            DECLARE @FimDiaProd TIME;
            DECLARE @DiaFim DATE = @Hoje;

            -- 1. Encontra o início do dia de produção
            SELECT TOP 1 @InicioDiaProd = HoraInicio 
            FROM TBL_Turno 
            WHERE Ativo = 1 AND IniciaDiaAnterior = 0
            ORDER BY HoraInicio ASC;
            
            IF @InicioDiaProd IS NULL
            BEGIN
                SELECT TOP 1 @InicioDiaProd = HoraInicio 
                FROM TBL_Turno 
                WHERE Ativo = 1
                ORDER BY HoraInicio ASC;
            END

            -- 2. Encontra o fim do dia de produção
            IF EXISTS (SELECT 1 FROM TBL_Turno WHERE Ativo = 1 AND IniciaDiaAnterior = 1)
            BEGIN
                SET @DiaFim = @Amanha;
                SELECT TOP 1 @FimDiaProd = HoraFim 
                FROM TBL_Turno 
                WHERE Ativo = 1 AND IniciaDiaAnterior = 1 
                ORDER BY HoraFim DESC;
            END
            ELSE
            BEGIN
                SELECT TOP 1 @FimDiaProd = HoraFim 
                FROM TBL_Turno 
                WHERE Ativo = 1 
                ORDER BY HoraFim DESC;
            END

            -- 3. Padrões de segurança (Fallback para 00:00 - 23:59)
            SET @InicioDiaProd = ISNULL(@InicioDiaProd, '00:00:00');
            SET @FimDiaProd = ISNULL(@FimDiaProd, '23:59:59');
            
            -- Correção de lógica: Se o fim do dia é hoje, mas o fim é ANTES do início
            -- (ex: único turno é T3 das 22:00 às 06:00), força o fim para amanhã.
            IF @DiaFim = @Hoje AND @FimDiaProd < @InicioDiaProd
            BEGIN
                SET @DiaFim = @Amanha;
            END

            -- 4. Constrói os timestamps (MÉTODO ROBUSTO COM CONVERT)
            --    Formato 23 = YYYY-MM-DD, Formato 8 = HH:MM:SS
            DECLARE @InicioDiaProducao DATETIME2 = CONVERT(DATETIME2, CONVERT(VARCHAR, @Hoje, 23) + ' ' + CONVERT(VARCHAR, @InicioDiaProd, 8));
            DECLARE @FimDiaProducao DATETIME2 = CONVERT(DATETIME2, CONVERT(VARCHAR, @DiaFim, 23) + ' ' + CONVERT(VARCHAR, @FimDiaProd, 8));

            -- 5. DEBUG: Retorna os valores calculados E a soma
            SELECT 
                ISNULL(SUM(prod.Quantidade), 0) AS ProducaoTotal,
                @InicioDiaProducao AS PeriodoInicio,
                @FimDiaProducao AS PeriodoFim
            FROM VW_EventoProducaoComCicloReal AS prod
            JOIN TBL_Recurso AS rec ON prod.IDMaquina = rec.IDMaquina
            WHERE prod.TipoValor = 'BOA'
              AND prod.DataHoraEvento BETWEEN @InicioDiaProducao AND @FimDiaProducao
              AND rec.Ativo = 1;
        """
        cursor_local.execute(query_producao_debug_v4)
        debug_result = cursor_local.fetchone()
        
        if debug_result:
            producao_hoje = debug_result.ProducaoTotal
            # Log para o console do servidor
            logger.info(f"DEBUG KPI HOME (V4): Período de produção: {debug_result.PeriodoInicio} a {debug_result.PeriodoFim}. Produção encontrada: {producao_hoje}")
        else:
            logger.error("DEBUG KPI HOME (V4): A query de produção V4 não retornou NENHUMA linha.")
            producao_hoje = 0
        # --- FIM DA ALTERAÇÃO (V4 - ROBUSTA COM CONVERT) ---

        # 3. Eficiência (OEE)
        id_turno_atual = identificar_turno(conn_local, cursor_local)
        if id_turno_atual:
            query_oee_recente = """
                WITH UltimoOEE_PorMaquina AS (
                    SELECT
                        IDMaquina, OEE,
                        ROW_NUMBER() OVER(PARTITION BY IDMaquina ORDER BY DataHoraCalculo DESC) as rn
                    FROM TBL_IndiceOEE
                    WHERE IDTurno = ? AND IDMaquina IN (SELECT DISTINCT IDMaquina FROM TBL_ExecucaoOP WHERE Status = 'Em Execucao')
                )
                SELECT AVG(OEE) as OEE_Medio_Recente FROM UltimoOEE_PorMaquina WHERE rn = 1;
            """
            cursor_local.execute(query_oee_recente, (id_turno_atual,))
            resultado_oee = cursor_local.fetchone()
            if resultado_oee and resultado_oee.OEE_Medio_Recente is not None:
                oee_final = resultado_oee.OEE_Medio_Recente * 100

        # 4. Total de Alertas
        cursor_local.execute("SELECT COUNT(*) FROM TBL_LogAlarmes WHERE Status = 'ATIVO'")
        total_alertas_row = cursor_local.fetchone()
        if total_alertas_row:
            total_alertas = total_alertas_row[0]
        
        return render_template('home.html',
                               total_maquinas=total_maquinas_ativas,
                               producao_hoje=producao_hoje,
                               eficiencia=oee_final,
                               alertas=total_alertas)

    except Exception as e:
        # Se qualquer parte falhar
        logger.error(f"Erro CRÍTICO ao carregar a página home (v4 debug): {e}", exc_info=True)
        # Retorna 0 para todos os KPIs para não quebrar a página
        return render_template('home.html', total_maquinas=0, producao_hoje=0, eficiencia=0, alertas=0)
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/cadastro_grupo_usuario', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_grupo_usuario')
def cadastro_grupo_usuario():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            id_grupo_form = request.form.get('id_grupo')
            nome = request.form['nome']
            codigo = request.form['codigo']
            ativo = 1 if 'ativo' in request.form else 0
            recebe_relatorio = 1 if 'recebe_relatorio' in request.form else 0
            recebe_alerta_estoque = 1 if 'recebe_alerta_estoque' in request.form else 0
            
            # --- INÍCIO DA ALTERAÇÃO ---
            # Captura o valor do novo checkbox do formulário
            pode_reconhecer_alerta = 1 if 'pode_reconhecer_alerta' in request.form else 0
            # --- FIM DA ALTERAÇÃO ---

            if id_grupo_form:
                if int(id_grupo_form) == 1:
                    cursor_local.execute("""
                        UPDATE TBL_GrupoUsuario 
                        SET NomeGrupo = ?, Ativo = ?, RecebeRelatorioOEE = ?, RecebeAlertaEstoque = ?, PodeReconhecerAlerta = ?
                        WHERE IDGrupo = ?
                    """, (nome, ativo, recebe_relatorio, recebe_alerta_estoque, pode_reconhecer_alerta, id_grupo_form))
                    flash("Grupo 'admin' atualizado com sucesso! (O código não pode ser alterado).", "info")
                else:
                    # --- ALTERAÇÃO: Adicionado "PodeReconhecerAlerta" ao UPDATE ---
                    cursor_local.execute("""
                        UPDATE TBL_GrupoUsuario 
                        SET NomeGrupo = ?, CodigoGrupo = ?, Ativo = ?, RecebeRelatorioOEE = ?, RecebeAlertaEstoque = ?, PodeReconhecerAlerta = ?
                        WHERE IDGrupo = ?
                    """, (nome, codigo, ativo, recebe_relatorio, recebe_alerta_estoque, pode_reconhecer_alerta, id_grupo_form))
                    flash("Grupo atualizado com sucesso!", "success")
            else:
                # --- ALTERAÇÃO: Adicionado "PodeReconhecerAlerta" ao INSERT ---
                cursor_local.execute("""
                    INSERT INTO TBL_GrupoUsuario (NomeGrupo, CodigoGrupo, Ativo, RecebeRelatorioOEE, RecebeAlertaEstoque, PodeReconhecerAlerta) 
                    VALUES (?, ?, ?, ?, ?, ?)
                """, (nome, codigo, ativo, recebe_relatorio, recebe_alerta_estoque, pode_reconhecer_alerta))
                flash("Grupo cadastrado com sucesso!", "success")
            
            conn_local.commit()
            return redirect(url_for('cadastro_grupo_usuario'))

        # Lógica GET (a busca por "*" já inclui a nova coluna, então não precisa de alteração aqui)
        id_edicao = request.args.get('id')
        grupo_para_editar = None
        if id_edicao:
            cursor_local.execute("SELECT * FROM TBL_GrupoUsuario WHERE IDGrupo = ?", id_edicao)
            grupo_para_editar = cursor_local.fetchone()

        cursor_local.execute("SELECT * FROM TBL_GrupoUsuario ORDER BY NomeGrupo")
        grupos = cursor_local.fetchall()
        
        cursor_local.execute("SELECT IDPermissao, Rota, NomeAmigavel, Topico FROM TBL_permissao ORDER BY Topico, NomeAmigavel")
        permissoes_raw = cursor_local.fetchall()
        permissoes_por_topico = defaultdict(list)
        for p in permissoes_raw:
            permissoes_por_topico[p.Topico].append({'id': p.IDPermissao, 'nome': p.NomeAmigavel})
            
        cursor_local.execute("SELECT IDGrupo, IDPermissao FROM TBL_PermissaoGrupo")
        permissoes_concedidas_raw = cursor_local.fetchall()
        permissao_por_grupo = defaultdict(list)
        for pc in permissoes_concedidas_raw:
            permissao_por_grupo[pc.IDGrupo].append(pc.IDPermissao)
        
        return render_template('cadastro_grupo_usuario.html',
                               grupos=grupos,
                               grupo=grupo_para_editar,
                               permissoes_por_topico=permissoes_por_topico,
                               permissao_por_grupo=permissao_por_grupo)
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em cadastro_grupo_usuario: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar a página de grupos.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local: devolver_conexao(conn_local)

# Editar Grupo
@app.route('/editar_grupo', methods=['POST'])
@login_requerido
@permissao_requerida('/cadastro_grupo_usuario')
def editar_grupo():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_grupo = request.form['id_grupo']
        permissoes_liberadas = request.form.getlist('permissao')
        novas_permissooes_json = request.form.get('novas_permissoes') # Renomeado para evitar conflito

        novas_permissoes = []
        if novas_permissooes_json:
            try:
                novas_permissoes = json.loads(novas_permissooes_json)
            except json.JSONDecodeError:
                logger.warning(f"Erro ao decodificar JSON de novas_permissoes: {novas_permissooes_json}")

        # Primeiro, adicionar novas permissões se ainda não existirem para o grupo específico
        for nova_rota in novas_permissoes:
            cursor_local.execute(
                "SELECT COUNT(*) AS qtd FROM TBL_PermissaoGrupo WHERE IDGrupo = ? AND Rota = ?", 
                (id_grupo, nova_rota)
            )
            qtd = cursor_local.fetchone().qtd
            if qtd == 0:
                cursor_local.execute(
                    "INSERT INTO TBL_PermissaoGrupo (IDGrupo, Rota, PodeAcessar) VALUES (?, ?, 0)", 
                    (id_grupo, nova_rota)
                )
                
        # Agora, resetar todas permissões do grupo para 0
        cursor_local.execute(
            "UPDATE TBL_PermissaoGrupo SET PodeAcessar = 0 WHERE IDGrupo = ?", 
            (id_grupo,)
        )

        # Depois, ativar somente as permissões que ficaram no lado liberadas
        for rota in permissoes_liberadas:
            cursor_local.execute(
                """
                UPDATE TBL_PermissaoGrupo
                SET PodeAcessar = 1
                WHERE IDGrupo = ? AND Rota = ?
                """,
                (id_grupo, rota)
            )
        conn_local.commit()
        flash("Permissões do grupo atualizadas com sucesso!", "success")
        return redirect(url_for('cadastro_grupo'))
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em editar_grupo: {e}", exc_info=True)
        flash("Ocorreu um erro ao atualizar as permissões do grupo.", "error")
        return redirect(url_for('cadastro_grupo'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)


# Em planner_app.py, substitua a função permissoes() inteira por esta:
# Adicione esta nova rota ao seu arquivo planner_app.py

@app.route('/api/grupo/<int:grupo_id>/permissoes', methods=['POST'])
@login_requerido
@somente_admin # Garante que apenas administradores podem alterar permissões
def salvar_permissoes_grupo(grupo_id):
    conn_local = None
    try:
        # Pega a lista de IDs das permissões que foram marcadas no formulário
        permissoes_selecionadas_ids = request.form.getlist('permissoes[]')

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Estratégia de atualização:
        # 1. Apaga todas as permissões antigas para este grupo.
        cursor_local.execute("DELETE FROM TBL_PermissaoGrupo WHERE IDGrupo = ?", grupo_id)

        # 2. Insere as novas permissões que foram selecionadas.
        if permissoes_selecionadas_ids:
            for permissao_id in permissoes_selecionadas_ids:
                cursor_local.execute(
                    "INSERT INTO TBL_PermissaoGrupo (IDGrupo, IDPermissao) VALUES (?, ?)",
                    (grupo_id, int(permissao_id))
                )

        conn_local.commit()
        
        # Retorna uma resposta de sucesso para o JavaScript
        return jsonify({'success': True, 'message': 'Permissões atualizadas com sucesso!'})

    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro ao salvar permissões para o grupo {grupo_id}: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Ocorreu um erro interno no servidor.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
            
@app.route('/permissoes', methods=['GET', 'POST'])
@login_requerido
@somente_admin # Garante que apenas o admin (IDGrupo=1) acesse
def permissoes():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Lógica para cadastrar uma nova permissão
        if request.method == 'POST':
            rota = request.form.get('rota')
            nome_amigavel = request.form.get('nome_amigavel')
            topico = request.form.get('topico')

            if not all([rota, nome_amigavel, topico]):
                flash("Todos os campos são obrigatórios.", "danger")
            elif not rota.startswith('/'):
                flash("A rota deve obrigatoriamente começar com '/'.", "danger")
            else:
                cursor_local.execute("SELECT IDPermissao FROM TBL_permissao WHERE Rota = ?", rota)
                if cursor_local.fetchone():
                    flash(f"A rota '{rota}' já está cadastrada.", "warning")
                else:
                    cursor_local.execute(
                        "INSERT INTO TBL_permissao (Rota, NomeAmigavel, Topico) VALUES (?, ?, ?)",
                        (rota, nome_amigavel, topico)
                    )
                    conn_local.commit()
                    flash(f"Permissão '{nome_amigavel}' cadastrada com sucesso!", "success")
            
            return redirect(url_for('permissoes'))

        # Lógica para exibir todas as permissões cadastradas
        cursor_local.execute("SELECT Topico, NomeAmigavel, Rota FROM TBL_permissao ORDER BY Topico, NomeAmigavel")
        permissoes_raw = cursor_local.fetchall()
        
        permissoes_agrupadas = defaultdict(list)
        for p in permissoes_raw:
            permissoes_agrupadas[p.Topico].append(p)

        return render_template('permissoes.html', permissoes_agrupadas=permissoes_agrupadas)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em /permissoes: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerenciar o catálogo de permissões.", "danger")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
           
@app.route('/cadastro_usuario', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_usuario')
def cadastro_usuario():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            id_usuario = request.form.get('id_usuario')
            nome = request.form['nome']
            registro = request.form['registro']
            codigo = request.form['codigo']
            senha = request.form['senha']
            grupo = request.form['grupo']
            email = request.form.get('email')
            ativo = 1 if 'ativo' in request.form else 0
            
            operador_flag = 1 if 'operador' in request.form else 0

            if id_usuario:
                # Lógica de ATUALIZAÇÃO
                cursor_local.execute("""
                    UPDATE TBL_Usuario
                    SET NomeUsuario = ?, RegistroFuncional = ?, CodigoUsuario = ?, 
                        IDGrupo = ?, Ativo = ?, Email = ?, Operador = ?
                    WHERE IDUsuario = ?
                """, (nome, registro, codigo, grupo, ativo, email, operador_flag, id_usuario))

                if senha:
                    senha_hash = generate_password_hash(senha)
                    cursor_local.execute("UPDATE TBL_Usuario SET Senha = ? WHERE IDUsuario = ?", (senha_hash, id_usuario))
                
                flash("Usuário atualizado com sucesso!", "success")
                novo_id = None # Garante que a variável exista para a lógica de sincronização
            else:
                # Lógica de NOVO CADASTRO
                if not senha:
                    flash("O campo Senha é obrigatório para novos usuários.", "error")
                    return redirect(url_for('cadastro_usuario'))
                
                senha_hash = generate_password_hash(senha)
                
                sql_insert_usuario = """
                    INSERT INTO TBL_Usuario (NomeUsuario, RegistroFuncional, CodigoUsuario, Senha, IDGrupo, Ativo, Email, Operador)
                    OUTPUT INSERTED.IDUsuario
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """
                
                novo_id = cursor_local.execute(sql_insert_usuario, nome, registro, codigo, senha_hash, grupo, ativo, email, operador_flag).fetchval()

                flash("Usuário cadastrado com sucesso!", "success")

            # Lógica de Sincronização com TBL_Operador
            if operador_flag == 1:
                cursor_local.execute("SELECT IDOperador FROM TBL_Operador WHERE IDUsuario = ?", (id_usuario or novo_id,))
                operador_existente = cursor_local.fetchone()
                if not operador_existente:
                    cursor_local.execute("INSERT INTO TBL_Operador (IDUsuario, NomeOperador, Ativo) VALUES (?, ?, ?)", (id_usuario or novo_id, nome, ativo))
                else:
                    # Garante que nome e status do operador estejam sincronizados com o status do usuário
                    cursor_local.execute("UPDATE TBL_Operador SET NomeOperador = ?, Ativo = ? WHERE IDUsuario = ?", (nome, ativo, id_usuario or novo_id))
            else:
                # <<< ALTERAÇÃO AQUI: Em vez de deletar, apenas inativa o operador >>>
                # Se a flag foi desmarcada, INATIVA o usuário na tabela de operadores para manter o histórico
                cursor_local.execute("UPDATE TBL_Operador SET Ativo = 0 WHERE IDUsuario = ?", (id_usuario or novo_id,))
            
            conn_local.commit()
            return redirect(url_for('cadastro_usuario'))

        # Lógica GET (para exibir a página)
        cursor_local.execute("SELECT IDGrupo, NomeGrupo FROM TBL_GrupoUsuario WHERE Ativo = 1")
        grupos = cursor_local.fetchall()

        cursor_local.execute("""
            SELECT U.IDUsuario, U.NomeUsuario, U.RegistroFuncional, U.CodigoUsuario, U.Ativo, 
                   U.Email, G.NomeGrupo, G.IDGrupo, U.Operador
            FROM TBL_Usuario U
            LEFT JOIN TBL_GrupoUsuario G ON U.IDGrupo = G.IDGrupo
            ORDER BY U.NomeUsuario
        """)
        usuarios = cursor_local.fetchall()

        id_edicao = request.args.get('id')
        usuario_editar = None
        if id_edicao:
            cursor_local.execute("SELECT * FROM TBL_Usuario WHERE IDUsuario = ?", id_edicao)
            usuario_editar = cursor_local.fetchone()

        return render_template('cadastro_usuario.html',
                           usuarios=usuarios,
                           grupos=grupos,
                           usuario_editar=usuario_editar)
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em cadastro_usuario: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar o cadastro/consulta de usuários.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
                       
@app.route('/teste_maquinas')
@login_requerido
def teste_maquinas():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("SELECT IDMaquina, NomeMaquina, CodigoInterno FROM TBL_Recurso WHERE Ativo = 1")
        maquinas = cursor_local.fetchall()
        
        maquinas_list = []
        for maquina in maquinas:
            maquinas_list.append({
                'IDMaquina': maquina.IDMaquina,
                'NomeMaquina': maquina.NomeMaquina,
                'CodigoInterno': maquina.CodigoInterno
            })
        
        logger.info(f"Total de máquinas ativas encontradas: {len(maquinas_list)}")
        for i, maq in enumerate(maquinas_list):
            logger.info(f"Máquina {i+1}: ID={maq['IDMaquina']}, Nome={maq['NomeMaquina']}")
        
        return render_template('teste_maquinas.html', maquinas=maquinas_list)
    
    except Exception as e:
        logger.error(f"Erro ao testar máquinas: {str(e)}", exc_info=True)
        flash("Ocorreu um erro ao carregar as máquinas.", "error")
        return f"Erro: {str(e)}"                       
    finally:
        if conn_local:
            devolver_conexao(conn_local)
@app.route('/cadastro_produto/', defaults={'produto_id': None}, methods=['GET', 'POST'])
@app.route('/cadastro_produto/<int:produto_id>', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_produto')
def cadastro_produto(produto_id):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Busca configurações
        usa_unidades_caixa = (obter_configuracao('USA_UNIDADES_POR_CAIXA', conn_local, cursor_local) == 'true')
        usa_campo_descricao = (obter_configuracao('USA_CAMPO_DESCRICAO_PRODUTO', conn_local, cursor_local) == 'true')

        # Busca Tipos de Produto para o Dropdown (Incluindo Codigo para o Front-end usar)
        cursor_local.execute("SELECT IDTipoProduto, Nome, Codigo FROM TBL_TipoProduto WHERE Ativo = 1 ORDER BY Nome")
        tipos_produto = cursor_local.fetchall()

        if request.method == 'POST':
            id_produto_form = request.form.get('id_produto')
            codigo = request.form.get('codigo')
            nome = request.form.get('nome')
            descricao = request.form.get('descricao') if usa_campo_descricao else None
            id_tipo_produto = request.form.get('id_tipo_produto')

            unidades_por_caixa_str = request.form.get('unidades_por_caixa')
            unidades_por_caixa = int(unidades_por_caixa_str) if usa_unidades_caixa and unidades_por_caixa_str and unidades_por_caixa_str.isdigit() and int(unidades_por_caixa_str) > 0 else None
            
            # ==============================================================================
            # INÍCIO DA CORREÇÃO (BLINDAGEM CONTRA VALORES VAZIOS)
            # ==============================================================================
            
            # 1. Captura os valores brutos do formulário (podem vir vazios se for MP)
            tempo_ciclo_raw = request.form.get('tempo_ciclo', '')
            fator_raw = request.form.get('fator', '')
            pulsos_raw = request.form.get('pulsos_por_producao', '')
            unidade_tempo_ciclo = request.form.get('unidade_tempo_ciclo')

            # 2. Tratamento Manual: Se vier vazio ou só espaços, força valor padrão seguro
            
            # Tempo de Ciclo -> 0
            if not tempo_ciclo_raw or tempo_ciclo_raw.strip() == '': 
                tempo_ciclo_valor = '0'
            else:
                tempo_ciclo_valor = tempo_ciclo_raw.replace(',', '.')

            # Fator -> 1.0
            if not fator_raw or fator_raw.strip() == '':
                fator = '1.0'
            else:
                fator = fator_raw.replace(',', '.')

            # Pulsos -> 1
            if not pulsos_raw or pulsos_raw.strip() == '':
                pulsos_por_producao = 1
            else:
                pulsos_por_producao = pulsos_raw
            
            # 3. Lógica de conversão e cálculo final
            if unidade_tempo_ciclo in ['mt/min', 'mt/h']:
                # Se for unidade linear, converte direto (já garantimos que é número acima)
                try:
                    tempo_ciclo_para_salvar = float(tempo_ciclo_valor)
                except ValueError:
                    tempo_ciclo_para_salvar = 0.0
            else:
                # Se não for linear, chama a função helper.
                # TRUQUE DE SEGURANÇA: Se a unidade vier vazia (caso do MP), forçamos 's/un' 
                # para a função auxiliar não reclamar. O valor será 0 de qualquer forma.
                unidade_para_funcao = unidade_tempo_ciclo if unidade_tempo_ciclo else 's/un'
                
                # Chama a função original sem alterá-la, passando dados limpos
                tempo_ciclo_para_salvar = converter_tempo_ciclo_para_segundos(tempo_ciclo_valor, unidade_para_funcao)
            
            # ==============================================================================
            # FIM DA CORREÇÃO
            # ==============================================================================

            id_unidade = request.form.get('unidade')
            
            habilitado = 1 if 'habilitado' in request.form else 0 
            nome_documento = request.form.get('nome_documento').strip() or None

            if id_produto_form: # Atualização
                cursor_local.execute("""
                    UPDATE TBL_Produto SET CodigoProduto = ?, NomeProduto = ?, Descricao = ?, 
                        TempoCicloSegundos = ?, FatorMultiplicacao = ?, UnidadesPorCaixa = ?, 
                        IDUnidade = ?, Habilitado = ?, PulsosPorProducao = ?, NomeDocumentoTecnico = ?,
                        UnidadeCiclo = ?, IDTipoProduto = ?
                    WHERE IDProduto = ?
                """, (codigo, nome, descricao, tempo_ciclo_para_salvar, fator, unidades_por_caixa, id_unidade, 
                      habilitado, pulsos_por_producao, nome_documento, unidade_tempo_ciclo, id_tipo_produto, id_produto_form))
                
                flash("Produto atualizado com sucesso!", "success")
            
            else: # Novo cadastro
                cursor_local.execute("""
                    INSERT INTO TBL_Produto (CodigoProduto, NomeProduto, Descricao, TempoCicloSegundos, 
                     FatorMultiplicacao, UnidadesPorCaixa, IDUnidade, Habilitado, PulsosPorProducao, 
                     NomeDocumentoTecnico, UnidadeCiclo, IDTipoProduto)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (codigo, nome, descricao, tempo_ciclo_para_salvar, fator, unidades_por_caixa, id_unidade, 
                      habilitado, pulsos_por_producao, nome_documento, unidade_tempo_ciclo, id_tipo_produto))
                
                flash("Produto cadastrado com sucesso!", "success")

                # ==============================================================================
                # LÓGICA DE AUTOMAÇÃO DE MATÉRIA-PRIMA (MP)
                # ==============================================================================
                if id_tipo_produto:
                    # Descobre qual é o código desse tipo (Ex: 'MP', 'SA', 'PA')
                    cursor_local.execute("SELECT Codigo FROM TBL_TipoProduto WHERE IDTipoProduto = ?", id_tipo_produto)
                    tipo_selecionado = cursor_local.fetchone()

                    # Se o código do tipo for 'MP', dispara a automação
                    if tipo_selecionado and tipo_selecionado.Codigo == 'MP':
                        logger.info(f"Produto {codigo} é do tipo MP. Verificando existência em TBL_MateriaPrima...")
                        
                        cursor_local.execute("SELECT IDMateriaPrima FROM TBL_MateriaPrima WHERE CodigoMateriaPrima = ?", codigo)
                        existe_mp = cursor_local.fetchone()

                        if not existe_mp:
                            cursor_local.execute("""
                                INSERT INTO TBL_MateriaPrima 
                                (CodigoMateriaPrima, NomeMateriaPrima, Descricao, IDUnidade, Ativo, 
                                 PermiteEstorno, GeraAlertaEstoque, ConsumoDiario, PrazoEntregaDias, DtCriacao)
                                VALUES (?, ?, ?, ?, ?, 1, 0, 0, 0, GETDATE())
                            """, (codigo, nome, descricao, id_unidade, habilitado))
                            flash("Nota: O item também foi cadastrado automaticamente como Matéria-Prima.", "info")
                            logger.info(f"Automação: Item {codigo} replicado em TBL_MateriaPrima.")
                # ==============================================================================

            conn_local.commit()
            return redirect(url_for('consulta_produtos'))

        # --- LÓGICA GET (CARREGAR PÁGINA) ---
        produto_para_editar = None
        valor_ciclo_display = ''

        if produto_id:
            cursor_local.execute("SELECT * FROM TBL_Produto WHERE IDProduto = ?", produto_id)
            produto_para_editar = cursor_local.fetchone()
            
            if not produto_para_editar:
                flash("Produto não encontrado.", "error")
                return redirect(url_for('consulta_produtos'))
            
            valor_ciclo_display = produto_para_editar.TempoCicloSegundos if produto_para_editar else ''

        cursor_local.execute("SELECT IDUnidade, Sigla, NomeUnidade FROM TBL_UnidadeMedida WHERE Ativo = 1 ORDER BY NomeUnidade")
        unidades = cursor_local.fetchall()

        return render_template('cadastro_produto.html', 
                               unidades=unidades, 
                               produto=produto_para_editar,
                               valor_ciclo_display=valor_ciclo_display, 
                               usa_unidades_caixa=usa_unidades_caixa,
                               usa_campo_descricao=usa_campo_descricao,
                               tipos_produto=tipos_produto) # Passa os tipos para o HTML

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em cadastro_produto: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar o cadastro de produtos.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/consulta_produtos')
@login_requerido
@permissao_requerida('/consulta_produtos')
def consulta_produtos():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Configurações
        usa_unidades_caixa = (obter_configuracao('USA_UNIDADES_POR_CAIXA', conn_local, cursor_local) == 'true')
        usa_campo_descricao = (obter_configuracao('USA_CAMPO_DESCRICAO_PRODUTO', conn_local, cursor_local) == 'true')

        # Parâmetros de Paginação e Busca
        page = request.args.get('page', 1, type=int)
        per_page = 20
        search_term = request.args.get('search', '').strip()
        
        offset = (page - 1) * per_page

        # --- 1. Query para CONTAR total de registros (para saber quantas páginas existem) ---
        query_count = """
            SELECT COUNT(*) 
            FROM TBL_Produto p
            WHERE 1=1
        """
        params_count = []

        if search_term:
            query_count += " AND (p.CodigoProduto LIKE ? OR p.NomeProduto LIKE ?)"
            params_count.extend([f"%{search_term}%", f"%{search_term}%"])

        total_registros = cursor_local.execute(query_count, params_count).fetchval()
        total_pages = math.ceil(total_registros / per_page)

        # --- 2. Query para BUSCAR os dados da página atual ---
        # Adicionamos o JOIN com TBL_TipoProduto
        query_data = """
            SELECT p.*, u.Sigla, tp.Codigo AS CodigoTipo, tp.Nome AS NomeTipo
            FROM TBL_Produto p
            LEFT JOIN TBL_UnidadeMedida u ON p.IDUnidade = u.IDUnidade
            LEFT JOIN TBL_TipoProduto tp ON p.IDTipoProduto = tp.IDTipoProduto
            WHERE 1=1
        """
        params_data = []

        if search_term:
            query_data += " AND (p.CodigoProduto LIKE ? OR p.NomeProduto LIKE ?)"
            params_data.extend([f"%{search_term}%", f"%{search_term}%"])

        # Ordenação e Paginação (SQL Server)
        query_data += """
            ORDER BY p.NomeProduto
            OFFSET ? ROWS FETCH NEXT ? ROWS ONLY
        """
        params_data.extend([offset, per_page])

        cursor_local.execute(query_data, params_data)
        produtos = cursor_local.fetchall()

        return render_template('consulta_produtos.html', 
                               produtos=produtos, 
                               usa_unidades_caixa=usa_unidades_caixa,
                               usa_campo_descricao=usa_campo_descricao,
                               current_page=page,
                               total_pages=total_pages,
                               search_term=search_term)
        
    except Exception as e:
        logger.error(f"Erro em consulta_produtos: {e}", exc_info=True)
        flash("Ocorreu um erro ao consultar os produtos.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
   
# Alterar Status Produto
@app.route('/alterar_status_produto/<int:id_produto>/<int:status>')
@login_requerido
@permissao_requerida('/consulta_produtos') # Assume que a alteração de status é parte da consulta
def alterar_status_produto(id_produto, status):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("""
            UPDATE TBL_Produto
            SET Habilitado = ?
            WHERE IDProduto = ?
        """, (status, id_produto))
        conn_local.commit()
        flash("Status do produto alterado com sucesso!", "success")
        return redirect(url_for('consulta_produtos'))
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em alterar_status_produto: {e}", exc_info=True)
        flash("Ocorreu um erro ao alterar o status do produto.", "error")
        return redirect(url_for('consulta_produtos'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)


@app.route('/cadastro_recurso', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_recurso')
def cadastro_recurso():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            # ... (captura dos dados do form - id_segmento vem do form com name="segmento") ...
            id_recurso = request.form.get('id_recurso')
            nome = request.form['nome']
            codigo = request.form['codigo']
            tipo = request.form['tipo']
            id_setor = request.form.get('setor') if request.form.get('setor') != '' else None
            id_segmento = request.form.get('segmento') if request.form.get('segmento') != '' else None # Captura o IdSegmento do form
            # ... (restante da captura do form) ...
            turnos_selecionados = request.form.getlist('turnos_associados')
            ativo = 1 if 'ativo' in request.form else 0
            unidade_velocidade = request.form.get('unidade_velocidade')
            meta_oee = float(request.form.get('meta_oee', 85))
            meta_qualidade = float(request.form.get('meta_qualidade', 95))
            meta_disponibilidade = float(request.form.get('meta_disponibilidade', 90))
            meta_performance = float(request.form.get('meta_performance', 90))
            limite_inatividade = int(request.form.get('limite_inatividade', 30))
            intervalo_debounce = int(request.form.get('intervalo_debounce', 0))
            linear_html = 1 if 'linear' in request.form else 0
            Automatico = 1 if 'Automatico' in request.form else 0
            link_externo = request.form.get('link_externo') # Captura o link

            if id_recurso: # ATUALIZAÇÃO
                # ----- CORREÇÃO FINAL AQUI (USA IDSegmento com D maiúsculo) -----
                cursor_local.execute("""
                    UPDATE TBL_Recurso SET NomeMaquina = ?, CodigoInterno = ?, IDTipo = ?, IDSetor = ?, IDSegmento = ?, Ativo = ?,
                           MetaOEE = ?, MetaQualidade = ?, MetaDisponibilidade = ?, MetaPerformance = ?,
                           LimiteInatividadeSegundos = ?, UnidadeVelocidadePadrao = ?,
                           IntervaloDebounceSegundos = ?, Linear = ?, Automatico = ?, LinkExterno = ?
                    WHERE IDMaquina = ?
                """, (nome, codigo, tipo, id_setor, id_segmento, ativo, # <-- Usa IDSegmento
                       meta_oee, meta_qualidade, meta_disponibilidade, meta_performance,
                       limite_inatividade, unidade_velocidade, intervalo_debounce,
                       linear_html, Automatico, link_externo, # Adiciona link_externo
                       id_recurso))
                # -----------------------------------------------------------------

                cursor_local.execute("DELETE FROM TBL_RecursoTurno WHERE IDRecurso = ?", id_recurso)
                for id_turno in turnos_selecionados:
                    cursor_local.execute("INSERT INTO TBL_RecursoTurno (IDRecurso, IDTurno) VALUES (?, ?)", (id_recurso, id_turno))
                flash("Recurso atualizado com sucesso!", "success")
            else: # NOVO CADASTRO
                 # ----- CORREÇÃO FINAL AQUI (USA IDSegmento com D maiúsculo) -----
                cursor_local.execute("""
                    INSERT INTO TBL_Recurso (NomeMaquina, CodigoInterno, IDTipo, IDSetor, IDSegmento, Ativo,
                                             MetaOEE, MetaQualidade, MetaDisponibilidade, MetaPerformance,
                                             LimiteInatividadeSegundos, UnidadeVelocidadePadrao, IntervaloDebounceSegundos, Linear, Automatico, LinkExterno)
                    OUTPUT INSERTED.IDMaquina
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (nome, codigo, tipo, id_setor, id_segmento, ativo, # <-- Usa IDSegmento
                       meta_oee, meta_qualidade, meta_disponibilidade, meta_performance,
                       limite_inatividade, unidade_velocidade, intervalo_debounce,
                       linear_html, Automatico, link_externo)) # Adiciona link_externo
                # ------------------------------------------------------------------

                novo_id_recurso = cursor_local.fetchone()[0]
                for id_turno in turnos_selecionados:
                    cursor_local.execute("INSERT INTO TBL_RecursoTurno (IDRecurso, IDTurno) VALUES (?, ?)", (novo_id_recurso, id_turno))
                flash("Recurso cadastrado com sucesso!", "success")

            conn_local.commit()
            return redirect(url_for('cadastro_recurso'))

        # --- Lógica GET ---
        recursos_dict = {}
        # Query já corrigida na resposta anterior para usar IdSegmento no JOIN e NomeSegmento no SELECT
        cursor_local.execute("""
            SELECT r.*, t.NomeTipo, s.Nome AS NomeSetor, seg.NomeSegmento AS NomeSegmento, tu.NomeTurno, tu.IDTurno
            FROM TBL_Recurso r
            LEFT JOIN TBL_TipoRecurso t ON r.IDTipo = t.IDTipo
            LEFT JOIN TBL_Setor s ON r.IDSetor = s.IDSetor
            LEFT JOIN dbo.TBL_SegmentoMaquina seg ON r.IDSegmento = seg.IdSegmento -- JOIN correto
            LEFT JOIN TBL_RecursoTurno rt ON r.IDMaquina = rt.IDRecurso
            LEFT JOIN TBL_Turno tu ON rt.IDTurno = tu.IDTurno
            ORDER BY r.NomeMaquina, tu.NomeTurno
        """)

        for row in cursor_local.fetchall():
            if row.IDMaquina not in recursos_dict:
                recursos_dict[row.IDMaquina] = {
                    'IDMaquina': row.IDMaquina, 'NomeMaquina': row.NomeMaquina, 'CodigoInterno': row.CodigoInterno,
                    'Ativo': row.Ativo, 'NomeTipo': row.NomeTipo, 'NomeSetor': row.NomeSetor,
                    'NomeSegmento': row.NomeSegmento,
                    'Turnos': [],
                    'LimiteInatividadeSegundos': row.LimiteInatividadeSegundos,
                    'UnidadeVelocidadePadrao': row.UnidadeVelocidadePadrao,
                    'IntervaloDebounceSegundos': row.IntervaloDebounceSegundos,
                    'linear': row.Linear,
                    'Automatico': row.Automatico,
                    'MetaOEE': row.MetaOEE, 'MetaQualidade': row.MetaQualidade,
                    'MetaDisponibilidade': row.MetaDisponibilidade, 'MetaPerformance': row.MetaPerformance,
                    'IDTipo': row.IDTipo, 'IDSetor': row.IDSetor,
                    # ----- CORREÇÃO FINAL AQUI (USA IDSegmento com D maiúsculo do objeto row) -----
                    'IDSeguimento': row.IDSegmento, # Acessa o atributo correto retornado por r.*
                    # ------------------------------------------------------------------------------
                    'LinkExterno': row.LinkExterno # Adiciona o link ao dict
                }
            if row.NomeTurno:
                recursos_dict[row.IDMaquina]['Turnos'].append(row.NomeTurno)
        recursos = list(recursos_dict.values())

        # ... (busca de tipos, setores, segmentos, turnos) ...
        cursor_local.execute("SELECT * FROM TBL_TipoRecurso")
        tipos = cursor_local.fetchall()
        cursor_local.execute("SELECT IDSetor, Nome, Codigo FROM TBL_Setor WHERE Ativo = 1 ORDER BY Nome")
        setores = cursor_local.fetchall()
        cursor_local.execute("SELECT IdSegmento, CodigoSegmento, NomeSegmento FROM TBL_SegmentoMaquina ORDER BY NomeSegmento")
        segmentos = cursor_local.fetchall()
        cursor_local.execute("SELECT IDTurno, NomeTurno FROM TBL_Turno WHERE Ativo = 1 ORDER BY NomeTurno")
        todos_turnos = cursor_local.fetchall()


        recurso_editar = None
        turnos_atribuidos_ids = []
        id_edicao = request.args.get('id')

        if id_edicao:
            # SELECT * buscará IDSegmento e LinkExterno
            cursor_local.execute("SELECT * FROM TBL_Recurso WHERE IDMaquina = ?", id_edicao)
            recurso_editar = cursor_local.fetchone()
            if not recurso_editar:
                 flash("Recurso não encontrado para edição.", "warning")
                 return redirect(url_for('cadastro_recurso'))

            cursor_local.execute("SELECT IDTurno FROM TBL_RecursoTurno WHERE IDRecurso = ?", id_edicao)
            turnos_atribuidos_ids = [row.IDTurno for row in cursor_local.fetchall()]

        return render_template(
            'cadastro_recurso.html',
            recurso_editar=recurso_editar,
            recursos=recursos,
            tipos=tipos,
            setores=setores,
            segmentos=segmentos,
            todos_turnos=todos_turnos,
            turnos_atribuidos_ids=turnos_atribuidos_ids
        )

    # ... (blocos except/finally) ...
    except pyodbc.ProgrammingError as pe:
        logger.error(f"Erro de Programação SQL em cadastro_recurso: {pe}", exc_info=True)
        flash(f"Erro de Banco de Dados: {pe}. Verifique se todas as colunas necessárias existem nas tabelas.", "error")
        return redirect(url_for('home'))
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro geral em cadastro_recurso: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar o cadastro/consulta de recursos.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local: devolver_conexao(conn_local)





# --- ROTAS DE INTEGRAÇÃO COM DISPOSITIVOS (ESP32) ---

@app.route('/status_maquina', methods=['POST'])
def status_maquina():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        data = request.get_json()
        logger.info(f"Dados recebidos em /status_maquina: {data}")
        
        id_maquina = data.get('id_maquina')
        status = data.get('status')  # 1 = Produzindo, 0 = Parada
        id_motivo_parada = data.get('id_motivo_parada')
        obs_evento = data.get('obs_evento', '')
        
        if id_maquina is None or status is None:
            return jsonify({"status": "error", "message": "Parâmetros incompletos"}), 400
            
        cursor_local.execute("SELECT IDMaquina FROM TBL_Recurso WHERE IDMaquina = ?", id_maquina)
        maquina = cursor_local.fetchone()
        
        if not maquina:
            return jsonify({"status": "error", "message": f"Máquina com ID {id_maquina} não encontrada"}), 404
            
        if status == 0 and not id_motivo_parada:
            return jsonify({
                "status": "error", 
                "message": "É necessário informar o motivo da parada"
            }), 400
        
        # --- Chamar a nova função auxiliar para atualizar o status ---
        success = _update_machine_status(conn_local, cursor_local, id_maquina, status, id_motivo_parada, obs_evento)
        
        if not success:
            raise Exception("Erro desconhecido ao atualizar status da máquina via _update_machine_status.")

        # Atualizar o status do dispositivo ESP32 (se existir)
        # Mantido como no seu código original
        timestamp = datetime.now()
        cursor_local.execute("""
            UPDATE pln_edu.dbo.TBL_DispositivoESP32 
            SET UltimaConexao = ?, Status = 1 
            WHERE IDMaquina = ?
        """, timestamp, id_maquina)
        
        conn_local.commit()
        
        # Obter o nome do status para a mensagem de resposta
        status_texto_resposta = "Desconhecido"
        try:
            cursor_local.execute("SELECT NomeStatus FROM TBL_TipoStatus WHERE Status = ?", status)
            row_status_text = cursor_local.fetchone()
            if row_status_text:
                status_texto_resposta = row_status_text.NomeStatus
        except Exception as e:
            logger.warning(f"Não foi possível obter NomeStatus para a mensagem de resposta: {e}")

        return jsonify({
            "status": "success", 
            "message": f"Status da máquina {id_maquina} atualizado para {status_texto_resposta}"
        })
        
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro ao atualizar status: {str(e)}", exc_info=True)
        return jsonify({"status": "error", "message": str(e)}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)


def verificar_virada_turno():
    """
    VERSÃO FINAL COM TRAVA DE BANCO DE DADOS (Process-Safe), CORREÇÃO DE IDSTATUS
    E CORREÇÃO DE SOMA DE QUANTIDADE PRODUZIDA.
    """
    # O lock de thread ainda é útil para evitar concorrência dentro do mesmo processo
    with virada_turno_lock:
        global last_known_system_turn_id
        conn_thread = None
        try:
            conn_thread = conectar_bd()
            cursor_thread = conn_thread.cursor()

            turno_atual = identificar_turno(conn_thread, cursor_thread)

            if last_known_system_turn_id is not None and turno_atual != last_known_system_turn_id:
                turno_finalizado = last_known_system_turn_id
                data_do_relatorio = datetime.now().date()

                logger.info(f"Virada de turno detectada: de {turno_finalizado} para {turno_atual}. Tentando registrar tarefa de envio de e-mail.")

                try:
                    # --- Lógica de Trava (DATABASE LOCK) ---
                    cursor_thread.execute("""
                        INSERT INTO TBL_LogRelatorioTurno (IDTurno, DataRelatorio, Status)
                        VALUES (?, ?, 'ENVIANDO')
                    """, (turno_finalizado, data_do_relatorio))
                    conn_thread.commit()
                    logger.info(f"Trava adquirida. Disparando relatório de OEE para o turno finalizado: {turno_finalizado}")
                    threading.Thread(target=enviar_relatorio_fim_turno, args=(turno_finalizado,)).start()

                except pyodbc.IntegrityError:
                    conn_thread.rollback()
                    logger.warning(f"Tarefa de envio para o turno {turno_finalizado} já foi iniciada por outro processo. Envio duplicado evitado.")
                # --- FIM DA LÓGICA DE TRAVA ---

                # ==============================================================================
                # BUSCAR ID STATUS 'EM EXECUCAO'
                # ==============================================================================
                cursor_thread.execute("SELECT IDStatus FROM TBL_StatusOrdemProducao WHERE NomeStatus = 'Em Execucao'")
                status_row = cursor_thread.fetchone()
                id_status_execucao = status_row.IDStatus if status_row else 5 
                # ==============================================================================

                cursor_thread.execute("SELECT DISTINCT IDMaquina FROM TBL_ExecucaoOP WHERE Status = 'Em Execucao'")
                maquinas_ativas = cursor_thread.fetchall()

                for maquina in maquinas_ativas:
                    id_maquina = maquina.IDMaquina

                    # 1. Buscar também o IDOrdemOperacao da execução recente
                    cursor_thread.execute("""
                        SELECT TOP 1 IDOrdem, IDOperador, QuantidadeProduzida, IDOrdemOperacao
                        FROM TBL_ExecucaoOP
                        WHERE IDMaquina = ? AND Status = 'Em Execucao'
                        ORDER BY DataHoraInicio DESC
                    """, id_maquina)
                    
                    execucao_recente = cursor_thread.fetchone()

                    if not execucao_recente: continue

                    id_ordem_continua = execucao_recente.IDOrdem
                    id_operador_continua = execucao_recente.IDOperador or 1 # Usar um operador padrão se for nulo
                    qtd_produzida_continua = execucao_recente.QuantidadeProduzida or 0
                    id_ordem_operacao_continua = execucao_recente.IDOrdemOperacao 

                    logger.info(f"Processando virada de turno para Máquina ID {id_maquina} (Ordem: {id_ordem_continua}, Operação: {id_ordem_operacao_continua}).")

                    # ==============================================================================
                    # CORREÇÃO PRINCIPAL AQUI: Atualiza a QuantidadeProduzida ao fechar por virada
                    # ==============================================================================
                    cursor_thread.execute("""
                        UPDATE TBL_ExecucaoOP
                        SET Status = 'Finalizada por Virada de Turno', 
                            DataHoraFim = GETDATE(),
                            QuantidadeProduzida = (
                                SELECT ISNULL(SUM(ev.Quantidade), 0)
                                FROM VW_EventoProducaoComCicloReal ev
                                WHERE ev.IDExecucao = TBL_ExecucaoOP.IDExecucao 
                                AND ev.TipoValor IN ('BOA', 'ESTORNO')
                            )
                        WHERE IDMaquina = ? AND Status = 'Em Execucao'
                    """, id_maquina)
                    # ==============================================================================

                    # CORREÇÃO: Inserir a nova execução COM IDStatus
                    cursor_thread.execute("""
                        INSERT INTO TBL_ExecucaoOP
                        (IDOrdem, IDMaquina, IDOperador, IDTurno, DataHoraInicio, Status, QuantidadeProduzida, IDOrdemOperacao, IDStatus)
                        VALUES (?, ?, ?, ?, GETDATE(), 'Em Execucao', ?, ?, ?)
                    """, (
                        id_ordem_continua, id_maquina, id_operador_continua, turno_atual,
                        qtd_produzida_continua,
                        id_ordem_operacao_continua,
                        id_status_execucao 
                    ))

                    # Log do evento
                    cursor_thread.execute("""
                        INSERT INTO TBL_EventoStatus (IDMaquina, Status, DataHoraEvento, ObsEvento)
                        VALUES (?, 1, GETDATE(), ?)
                    """, (id_maquina, f"Virada de turno de {last_known_system_turn_id} para {turno_atual}"))

                conn_thread.commit()

            last_known_system_turn_id = turno_atual

        except Exception as e:
            logger.error(f"Erro ao verificar virada de turno: {str(e)}", exc_info=True)
            if conn_thread:
                conn_thread.rollback()
        finally:
            if conn_thread:
                try:
                    conn_thread.close()
                except Exception as e:
                    logger.error(f"Erro ao fechar conexão do thread de virada de turno: {e}")
            

def verificar_virada_turno_periodicamente():
    """Loop para verificar virada de turno periodicamente."""
    while True:
        try:
            verificar_virada_turno() # Esta função gerencia sua própria conexão
            time.sleep(60) # Verificar a cada minuto
        except Exception as e:
            logger.error(f"Erro no thread de verificação de virada de turno: {str(e)}", exc_info=True)
            time.sleep(60) # Continua tentando mesmo em caso de erro

# Iniciar o thread de verificação de virada de turno
thread_virada_turno = threading.Thread(target=verificar_virada_turno_periodicamente, daemon=True)
thread_virada_turno.start()                

@app.route('/registrar_dispositivo', methods=['POST'])
def registrar_dispositivo():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        data = request.get_json()
        logger.info(f"Dados recebidos em /registrar_dispositivo: {data}")
        
        codigo = data.get('codigo')
        id_maquina = data.get('id_maquina')
        ip = data.get('ip')
        
        if not codigo or not id_maquina:
            return jsonify({"status": "error", "message": "Código do dispositivo e ID da máquina são obrigatórios"}), 400
            
        timestamp = datetime.now()
        
        cursor_local.execute("SELECT IDMaquina FROM TBL_Recurso WHERE IDMaquina = ?", id_maquina)
        maquina = cursor_local.fetchone()
        
        if not maquina:
            return jsonify({"status": "error", "message": f"Máquina com ID {id_maquina} não encontrada"}), 404
        
        cursor_local.execute("SELECT IDDispositivo FROM pln_edu.dbo.TBL_DispositivoESP32 WHERE CodigoDispositivo = ?", codigo)
        dispositivo = cursor_local.fetchone()
        
        if dispositivo:
            cursor_local.execute("""
                UPDATE pln_edu.dbo.TBL_DispositivoESP32 
                SET IDMaquina = ?, EnderecoIP = ?, UltimaConexao = ?, Status = 1 
                WHERE CodigoDispositivo = ?
            """, id_maquina, ip, timestamp, codigo)
            
            logger.info(f"Dispositivo {codigo} atualizado para máquina {id_maquina}")
        else:
            cursor_local.execute("""
                INSERT INTO pln_edu.dbo.TBL_DispositivoESP32 
                (CodigoDispositivo, IDMaquina, EnderecoIP, UltimaConexao, Status) 
                VALUES (?, ?, ?, ?, 1)
            """, codigo, id_maquina, ip, timestamp)
            
            logger.info(f"Novo dispositivo {codigo} registrado para máquina {id_maquina}")
        
        conn_local.commit()
        
        return jsonify({
            "status": "success", 
            "message": f"Dispositivo {codigo} registrado para máquina {id_maquina}",
            "timestamp": timestamp.isoformat()
        })
        
    except Exception as e:
        logger.error(f"Erro ao registrar dispositivo: {str(e)}", exc_info=True)
        return jsonify({"status": "error", "message": str(e)}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# --- ROTAS DE PRODUÇÃO E ORDENS ---

@app.route('/iniciar_execucao', methods=['POST'])
@login_requerido

def iniciar_execucao():
    conn_local = None
    try:
        id_ordem = request.form['id_ordem']
        id_maquina = request.form['id_maquina']
        id_operador = request.form['id_operador']

        logger.info(f"Iniciando execução (lógica corrigida): Ordem {id_ordem}, Máquina {id_maquina}")

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # --- INÍCIO DA CORREÇÃO ---
        # 1. Descobrir qual é a próxima operação pendente para esta ordem nesta máquina.
        cursor_local.execute("""
            SELECT TOP 1 IDOrdemOperacao 
            FROM TBL_OrdemProducao_Operacoes
            WHERE IDOrdem = ? AND IDRecurso = ? AND StatusOperacao = 'Pendente'
            ORDER BY Sequencia ASC
        """, (id_ordem, id_maquina))
        
        operacao_para_iniciar = cursor_local.fetchone()

        if not operacao_para_iniciar:
            flash(f"Não foi encontrada uma operação pendente para a Ordem {id_ordem} nesta máquina.", "error")
            return redirect(url_for('dashboard'))
            
        id_ordem_operacao = operacao_para_iniciar.IDOrdemOperacao
        # --- FIM DA CORREÇÃO ---

        id_turno = identificar_turno(conn_local, cursor_local)
        if id_turno is None:
            flash("Erro: Não foi possível identificar o turno atual para iniciar a execução.", "error")
            return redirect(url_for('dashboard'))

        # (A lógica para verificar produção anterior continua válida)
        cursor_local.execute("""
            SELECT ISNULL(SUM(ev.Quantidade), 0) as QuantidadeAnterior
            FROM VW_EventoProducaoComCicloReal ev
            JOIN TBL_ExecucaoOP ex ON ev.IDExecucao = ex.IDExecucao
            WHERE ex.IDOrdemOperacao = ? AND ev.TipoValor IN ('BOA', 'ESTORNO')
        """, (id_ordem_operacao,))
        resultado_soma = cursor_local.fetchone()
        quantidade_anterior = resultado_soma.QuantidadeAnterior if resultado_soma else 0
        
        # --- ALTERAÇÃO NO INSERT E LÓGICA DE FILA/STATUS ---
        # 2. Remover a operação específica da fila
        cursor_local.execute("DELETE FROM TBL_FilaOrdem WHERE IDOrdemOperacao = ?", (id_ordem_operacao,))

        # 3. Atualizar o status da operação e da ordem
        cursor_local.execute("UPDATE TBL_OrdemProducao_Operacoes SET StatusOperacao = 'Em Execucao' WHERE IDOrdemOperacao = ?", (id_ordem_operacao,))
        cursor_local.execute("UPDATE TBL_OrdemProducao SET IDStatus = 5 WHERE IDOrdem = ?", (id_ordem,))

        # 4. Inserir o novo registro de execução com o ID da operação e a quantidade anterior
        cursor_local.execute("""
            INSERT INTO TBL_ExecucaoOP 
            (IDOrdem, IDMaquina, IDOperador, IDTurno, DataHoraInicio, Status, IDOrdemOperacao, QuantidadeProduzida)
            VALUES (?, ?, ?, ?, GETDATE(), 'Em Execucao', ?, ?)
        """, (id_ordem, id_maquina, id_operador, id_turno, id_ordem_operacao, quantidade_anterior))
        
        conn_local.commit()
        flash(f"Execução iniciada com sucesso! Produção anterior de {float(quantidade_anterior):g} foi mantida.", "success")
        return redirect(url_for('dashboard'))
        
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro ao iniciar execução: {str(e)}", exc_info=True)
        flash(f"Erro ao iniciar execução: {str(e)}", "error")
        return redirect(url_for('dashboard'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
@app.route('/inserir_op', methods=['POST'])
@login_requerido
#@permissao_requerida('/inserir_op')
def inserir_op():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_maquina = request.form['id_maquina']
        id_ordem = request.form['id_ordem']
        id_ordem_operacao = request.form.get('id_ordem_operacao')
        acao = request.form['acao']

        # --- LÓGICA PARA "EXECUTAR" ---
        if acao == 'executar':
            cursor_local.execute("SELECT TOP 1 IDExecucao FROM TBL_ExecucaoOP WHERE IDMaquina = ? AND Status IN ('Em Execucao', 'Em Setup')", (id_maquina,))
            if cursor_local.fetchone():
                return jsonify({'status': 'error', 'message': 'Máquina já possui uma OP em execução ou em setup.'}), 409

            if not id_ordem_operacao:
                 return jsonify({'status': 'error', 'message': 'Erro: ID da operação não foi fornecido para iniciar a execução.'}), 400

            # Variáveis definidas apenas dentro deste bloco, onde são necessárias
            id_usuario_logado = session.get('usuario_id')
            cursor_local.execute("SELECT IDOperador FROM TBL_Operador WHERE IDUsuario = ? AND Ativo = 1", id_usuario_logado)
            operador = cursor_local.fetchone()
            id_operador_validado = operador.IDOperador if operador else None
            id_turno = identificar_turno(conn_local, cursor_local)

            # ==============================================================================
            # CORREÇÃO: Buscar o ID do Status "Em Execucao"
            # ==============================================================================
            cursor_local.execute("SELECT IDStatus FROM TBL_StatusOrdemProducao WHERE NomeStatus = 'Em Execucao'")
            status_row = cursor_local.fetchone()
            id_status_execucao = status_row.IDStatus if status_row else 5 
            # ==============================================================================

            # ==============================================================================
            # NOVO: VERIFICAÇÃO DE SEQUÊNCIA (BLOQUEIO DE SEGURANÇA)
            # ==============================================================================
            # Se quiser ativar o bloqueio de sequência aqui também, descomente a linha abaixo:
            # pode_iniciar, msg_erro = verificar_precedencia_operacao(cursor_local, id_ordem, id_ordem_operacao)
            # if not pode_iniciar:
            #      return jsonify({'status': 'error', 'message': msg_erro}), 400
            # ==============================================================================

            cursor_local.execute("DELETE FROM TBL_FilaOrdem WHERE IDOrdemOperacao = ?", (id_ordem_operacao,))
            
            # Busca produção anterior da operação
            cursor_local.execute("""
                SELECT ISNULL(SUM(ev.Quantidade), 0) as QuantidadeAnterior
                FROM VW_EventoProducaoComCicloReal ev
                JOIN TBL_ExecucaoOP ex ON ev.IDExecucao = ex.IDExecucao
                WHERE ex.IDOrdemOperacao = ? AND ev.TipoValor IN ('BOA', 'ESTORNO')
            """, (id_ordem_operacao,))
            resultado_soma = cursor_local.fetchone()
            quantidade_anterior = resultado_soma.QuantidadeAnterior if resultado_soma else 0

            # Cria a nova execução COM IDStatus
            cursor_local.execute("""
                INSERT INTO TBL_ExecucaoOP (IDOrdem, IDMaquina, IDOperador, IDTurno, DataHoraInicio, Status, IDOrdemOperacao, QuantidadeProduzida, IDStatus)
                VALUES (?, ?, ?, ?, GETDATE(), 'Em Execucao', ?, ?, ?)
            """, (id_ordem, id_maquina, id_operador_validado, id_turno, id_ordem_operacao, quantidade_anterior, id_status_execucao))

            cursor_local.execute("UPDATE TBL_OrdemProducao_Operacoes SET StatusOperacao = 'Em Execucao' WHERE IDOrdemOperacao = ?", (id_ordem_operacao,))
            cursor_local.execute("UPDATE TBL_OrdemProducao SET IDStatus = ? WHERE IDOrdem = ?", (id_status_execucao, id_ordem,))
            
            conn_local.commit()
            return jsonify({'status': 'success', 'message': 'OP iniciada com sucesso!'})

        # --- LÓGICA PARA "SEQUENCIAR" ---
        elif acao == 'fila':
            try:
                # Esta lógica é auto-contida e não depende de 'id_operador_validado'
                cursor_local.execute("INSERT INTO TBL_FilaOrdem (IDMaquina, IDOrdem, StatusFila, IDOrdemOperacao) VALUES (?, ?, 'pendente', ?)", (id_maquina, id_ordem, id_ordem_operacao))
                cursor_local.execute("UPDATE TBL_OrdemProducao SET IDStatus = 3 WHERE IDOrdem = ?", (id_ordem,))
                conn_local.commit()
                return jsonify({'status': 'success', 'message': 'OP sequenciada com sucesso!'})
            except pyodbc.IntegrityError:
                conn_local.rollback() # Garante que a transação seja desfeita
                return jsonify({'status': 'warning', 'message': 'Esta operação já está na fila desta máquina.'}), 409

        # Se a ação não for nenhuma das esperadas
        return jsonify({'status': 'error', 'message': 'Ação desconhecida.'}), 400

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro CRÍTICO em /inserir_op: {e}", exc_info=True)
        # --- CORREÇÃO CRÍTICA: Adiciona o retorno no bloco de exceção ---
        return jsonify({'status': 'error', 'message': f'Ocorreu um erro no servidor: {str(e)}'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/cadastro_ordem', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_ordem')
def cadastro_ordem():
    conn_local = None
    ID_STATUS_LIBERADA = 2
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            codigo_ordem = request.form.get('codigo')
            id_produto = request.form.get('produto')
            quantidade = request.form.get('quantidade')
            data_inicio_str = request.form.get('data_inicio')
            data_fim_str = request.form.get('data_fim')
            usar_tempo_ciclo_recurso = 1 if 'usar_tempo_ciclo_recurso' in request.form else 0
            fator_multiplicacao_ordem = request.form.get('fator_multiplicacao_ordem', 1.0)

            try:
                data_inicio = datetime.strptime(data_inicio_str, '%Y-%m-%d') if data_inicio_str else None
                data_fim = datetime.strptime(data_fim_str, '%Y-%m-%d') if data_fim_str else None
            except ValueError:
                flash("Formato de data inválido.", "error")
                return redirect(url_for('cadastro_ordem'))

            sequencias = request.form.getlist('op_sequencia')
            numeros_op = request.form.getlist('op_numero')
            descricoes = request.form.getlist('op_descricao')
            recursos_op = request.form.getlist('op_recurso')
            setups_op = request.form.getlist('op_tempo_setup')
            documentos_op = request.form.getlist('op_documento')
            
            # --- NOVO: Captura a lista de quantidades específicas por operação ---
            quantidades_op = request.form.getlist('op_quantidade')

            sql_insert_op = """
                INSERT INTO TBL_OrdemProducao (CodigoOrdem, IDProduto, QuantidadePlanejada, DataInicioPlanejada, DataFimPlanejada, IDStatus, UsarTempoCicloRecurso, FatorMultiplicacaoOrdem)
                OUTPUT INSERTED.IDOrdem VALUES (?, ?, ?, ?, ?, ?, ?, ?);
            """
            params_insert = (codigo_ordem, id_produto, quantidade, data_inicio, data_fim, ID_STATUS_LIBERADA, usar_tempo_ciclo_recurso, fator_multiplicacao_ordem)
            id_nova_ordem = cursor_local.execute(sql_insert_op, params_insert).fetchval()

            for i in range(len(sequencias)):
                if not sequencias[i] or not numeros_op[i] or not descricoes[i]:
                    logger.warning(f"Pulando linha de operação {i+1} por dados incompletos no cadastro da OP {codigo_ordem}")
                    continue

                tempo_setup_op = float(str(setups_op[i]).replace(',', '.')) if i < len(setups_op) and setups_op[i] else 0
                id_recurso_op = recursos_op[i] if i < len(recursos_op) and recursos_op[i] else None
                nome_documento_op = documentos_op[i].strip() or None if i < len(documentos_op) else None
                
                # --- NOVO: Lógica para definir a quantidade da operação ---
                # Se o campo específico estiver preenchido, usa-o. Caso contrário, usa a quantidade total da ordem.
                qtd_op_especifica = float(str(quantidades_op[i]).replace(',', '.')) if i < len(quantidades_op) and quantidades_op[i] else float(quantidade)

                # --- ATUALIZADO: Insert com QuantidadePlanejada ---
                id_nova_operacao = cursor_local.execute("""
                    INSERT INTO TBL_OrdemProducao_Operacoes 
                    (IDOrdem, Sequencia, NumeroOperacao, Descricao, IDRecurso, TempoSetupPlanejadoMinutos, StatusOperacao, NomeDocumentoTecnico, QuantidadePlanejada)
                    OUTPUT INSERTED.IDOrdemOperacao
                    VALUES (?, ?, ?, ?, ?, ?, 'Pendente', ?, ?)
                """, (id_nova_ordem, sequencias[i], numeros_op[i], descricoes[i], id_recurso_op, tempo_setup_op, nome_documento_op, qtd_op_especifica)).fetchval()

                if id_recurso_op and id_nova_operacao:
                    try:
                        cursor_local.execute("""
                            INSERT INTO TBL_FilaOrdem (IDMaquina, IDOrdem, StatusFila, IDOrdemOperacao)
                            VALUES (?, ?, 'pendente', ?)
                        """, (id_recurso_op, id_nova_ordem, id_nova_operacao))
                    except pyodbc.IntegrityError:
                        logger.warning(f"Tentativa de inserir operação duplicada na fila para NOVA OP {id_nova_ordem}, Maquina {id_recurso_op}. Ignorando.")
                        pass

            flash("Ordem cadastrada e suas operações foram alocadas nas filas!", "success")
            conn_local.commit()
            return redirect(url_for('cadastro_ordem'))

        else:
            # --- LÓGICA GET (sem alterações necessárias se o banco estiver atualizado) ---
            cursor_local.execute("SELECT IDProduto, CodigoProduto, NomeProduto, TempoCicloSegundos, FatorMultiplicacao FROM TBL_Produto WHERE Habilitado = 1 ORDER BY NomeProduto")
            produtos = cursor_local.fetchall()
            cursor_local.execute("SELECT IDMaquina, NomeMaquina, CodigoInterno FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina")
            recursos = cursor_local.fetchall()
            return render_template('cadastro_ordem.html',
                                   produtos=produtos,
                                   recursos=recursos,
                                   ordem=None,
                                   operacoes_ordem=[])

    except pyodbc.IntegrityError as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro de Integridade em cadastro_ordem: {e}", exc_info=True)
        flash(f"Erro de banco de dados ao salvar a ordem. Verifique se o Código da Ordem já existe. Detalhe: {e}", "danger")
        return redirect(url_for('cadastro_ordem'))
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro CRÍTICO em cadastro_ordem: {e}", exc_info=True)
        flash("Ocorreu um erro crítico ao salvar a ordem de produção.", "error")
        return redirect(url_for('cadastro_ordem'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/editar_ordem/<int:ordem_id>', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/editar_ordem') # Reutilizando a permissão de cadastro
def editar_ordem(ordem_id):
    conn_local = None
    # IDs de status (Idealmente definidos globalmente ou buscados no início)
    ID_STATUS_LIBERADA = 2
    ID_STATUS_INTERROMPIDA = 3
    ID_STATUS_FINALIZADA = 4
    ID_STATUS_EM_EXECUCAO = 5 # Apenas para referência
    ID_STATUS_EM_SETUP = 6    # Apenas para referência

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # --- LÓGICA POST (SALVAR ALTERAÇÕES - SÓ CABEÇALHO) ---
        if request.method == 'POST':
            id_ordem_form = request.form.get('id_ordem')
            if not id_ordem_form or int(id_ordem_form) != ordem_id:
                 flash("Erro de inconsistência no ID da Ordem.", "error")
                 return redirect(url_for('consulta_ordens'))

            # --- Buscar Status Atual ANTES de qualquer coisa ---
            cursor_local.execute("SELECT IDStatus FROM TBL_OrdemProducao WHERE IDOrdem = ?", id_ordem_form)
            status_atual_row = cursor_local.fetchone()
            if not status_atual_row:
                 flash("Erro: Ordem não encontrada para atualização.", "error")
                 return redirect(url_for('consulta_ordens'))
            status_atual_id = status_atual_row.IDStatus

            # --- Recuperar dados do formulário ---
            codigo_ordem = request.form.get('codigo')
            id_produto = request.form.get('produto')
            quantidade = request.form.get('quantidade')
            data_inicio_str = request.form.get('data_inicio')
            data_fim_str = request.form.get('data_fim')
            usar_tempo_ciclo_recurso = 1 if 'usar_tempo_ciclo_recurso' in request.form else 0
            fator_multiplicacao_ordem = request.form.get('fator_multiplicacao_ordem', 1.0)
            # A flag reverter_status_flag foi removida daqui, pois a ação agora é via API

            try:
                data_inicio = datetime.strptime(data_inicio_str, '%Y-%m-%d') if data_inicio_str else None
                data_fim = datetime.strptime(data_fim_str, '%Y-%m-%d') if data_fim_str else None
            except ValueError:
                flash("Formato de data inválido.", "error")
                return redirect(url_for('editar_ordem', ordem_id=id_ordem_form))

            # --- ATUALIZAR ORDEM PRINCIPAL (SEMPRE) ---
            # Atualiza apenas o cabeçalho. O status NÃO é alterado aqui,
            # exceto pela ação explícita de reabrir operação (em outra rota).
            cursor_local.execute("""
                UPDATE TBL_OrdemProducao SET
                    CodigoOrdem = ?, IDProduto = ?, QuantidadePlanejada = ?,
                    DataInicioPlanejada = ?, DataFimPlanejada = ?, -- IDStatus = ?, <-- REMOVIDO DAQUI
                    UsarTempoCicloRecurso = ?, FatorMultiplicacaoOrdem = ?
                WHERE IDOrdem = ?
            """, (codigo_ordem, id_produto, quantidade, data_inicio, data_fim, # Removido status_atual_id
                  usar_tempo_ciclo_recurso, fator_multiplicacao_ordem, id_ordem_form))

            # --- NÃO HÁ MAIS EXCLUSÃO/RECRIAÇÃO DE OPERAÇÕES/FILA AQUI ---
            # A edição do roteiro foi removida desta tela para preservar o histórico.

            flash("Alterações no cabeçalho da ordem salvas com sucesso!", "success")
            conn_local.commit()
            return redirect(url_for('consulta_ordens'))

        # --- LÓGICA GET (CARREGAR PÁGINA PARA EDIÇÃO) ---
        else:
            # Busca os dados da ordem específica
            cursor_local.execute("SELECT * FROM TBL_OrdemProducao WHERE IDOrdem = ?", ordem_id)
            ordem_para_editar = cursor_local.fetchone()
            if not ordem_para_editar:
                flash("Ordem de Produção não encontrada.", "error")
                return redirect(url_for('consulta_ordens'))

            # Busca as operações da ordem (incluindo status para o botão Reabrir)
            cursor_local.execute("""
                SELECT *,
                       CASE StatusOperacao WHEN 'Finalizada' THEN 1 ELSE 0 END as PodeReabrir
                FROM TBL_OrdemProducao_Operacoes
                WHERE IDOrdem = ? ORDER BY Sequencia
            """, ordem_id)
            operacoes_ordem = cursor_local.fetchall() # Agora contém StatusOperacao

            # Busca produtos e recursos para os dropdowns
            cursor_local.execute("SELECT IDProduto, CodigoProduto, NomeProduto, TempoCicloSegundos, FatorMultiplicacao FROM TBL_Produto WHERE Habilitado = 1 ORDER BY NomeProduto")
            produtos = cursor_local.fetchall()
            cursor_local.execute("SELECT IDMaquina, NomeMaquina, CodigoInterno FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina")
            recursos = cursor_local.fetchall()

            # Passa os dados para o template de edição
            return render_template('editar_ordem.html',
                                   ordem=ordem_para_editar,
                                   operacoes_ordem=operacoes_ordem, # Passa operações com status
                                   produtos=produtos,
                                   recursos=recursos)
                                   # ID_STATUS_FINALIZADA não é mais necessário aqui

    except pyodbc.IntegrityError as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro de Integridade em editar_ordem para OP ID {ordem_id}: {e}", exc_info=True)
        flash(f"Erro de banco de dados ao salvar a ordem. Verifique códigos duplicados ou dados inválidos. Detalhe: {e}", "danger")
        return redirect(url_for('editar_ordem', ordem_id=ordem_id))
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro CRÍTICO em editar_ordem para OP ID {ordem_id}: {e}", exc_info=True)
        flash("Ocorreu um erro crítico ao editar a ordem de produção.", "error")
        return redirect(url_for('consulta_ordens'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
@app.route('/reabrir_operacao/<int:id_ordem_operacao>', methods=['POST'])
@login_requerido
@permissao_requerida('/cadastro_ordem') # Ou crie '/reabrir_operacao' e adicione a permissão
def reabrir_operacao(id_ordem_operacao):
    conn_local = None
    # --- DEFINIÇÕES LOCAIS DOS STATUS NECESSÁRIOS ---
    # Certifique-se que estes IDs correspondem aos do seu banco TBL_StatusOrdemProducao
    ID_STATUS_INTERROMPIDA = 3
    ID_STATUS_FINALIZADA = 4
    # --- FIM DAS DEFINIÇÕES LOCAIS ---
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Buscar informações da operação
        cursor_local.execute("""
            SELECT IDOrdem, IDRecurso, StatusOperacao
            FROM TBL_OrdemProducao_Operacoes
            WHERE IDOrdemOperacao = ?
        """, (id_ordem_operacao,))
        operacao = cursor_local.fetchone()

        if not operacao:
            return jsonify({'success': False, 'message': 'Operação não encontrada.'}), 404

        if operacao.StatusOperacao != 'Finalizada':
            return jsonify({'success': False, 'message': f'A operação não está Finalizada (Status atual: {operacao.StatusOperacao}).'}), 400

        id_ordem = operacao.IDOrdem
        id_recurso = operacao.IDRecurso

        # 1. Mudar status da Operação para Pendente
        cursor_local.execute("""
            UPDATE TBL_OrdemProducao_Operacoes
            SET StatusOperacao = 'Pendente'
            WHERE IDOrdemOperacao = ?
        """, (id_ordem_operacao,))
        logger.info(f"Status da operação {id_ordem_operacao} alterado para Pendente.")

        # 2. Mudar status da Ordem para Interrompida (SE estava Finalizada)
        cursor_local.execute("""
            UPDATE TBL_OrdemProducao
            SET IDStatus = ?
            WHERE IDOrdem = ? AND IDStatus = ? -- Segurança: Só reabre se a ordem estava Finalizada
        """, (ID_STATUS_INTERROMPIDA, id_ordem, ID_STATUS_FINALIZADA)) # Usa as constantes definidas localmente
        if cursor_local.rowcount > 0:
             logger.info(f"Status da Ordem {id_ordem} alterado para Interrompida.")
        else:
             logger.info(f"Status da Ordem {id_ordem} já não era Finalizada, mantido.")


        # 3. Adicionar operação de volta à fila (se tiver recurso)
        if id_recurso:
            try:
                # Verifica se já existe na fila antes de inserir
                cursor_local.execute("SELECT 1 FROM TBL_FilaOrdem WHERE IDOrdemOperacao = ?", (id_ordem_operacao,))
                if not cursor_local.fetchone():
                    cursor_local.execute("""
                        INSERT INTO TBL_FilaOrdem (IDMaquina, IDOrdem, StatusFila, IDOrdemOperacao, OrdemFila)
                        SELECT ?, ?, 'pendente', ?, ISNULL(MAX(OrdemFila), 0) + 1
                        FROM TBL_FilaOrdem WHERE IDMaquina = ?
                    """, (id_recurso, id_ordem, id_ordem_operacao, id_recurso))
                    logger.info(f"Operação {id_ordem_operacao} adicionada à fila da máquina {id_recurso}.")
                    # Reordena a fila após a inserção
                    reordenar_fila(conn_local, cursor_local, id_recurso)
                else:
                    logger.info(f"Operação {id_ordem_operacao} já existe na fila da máquina {id_recurso}. Nenhuma ação na fila.")

            except Exception as e_fila:
                 logger.error(f"Erro ao tentar adicionar operação {id_ordem_operacao} à fila: {e_fila}")
                 # Continua mesmo se a fila falhar
        else:
            logger.warning(f"Operação {id_ordem_operacao} não possui recurso associado, não foi adicionada à fila.")

        conn_local.commit()
        return jsonify({'success': True, 'message': 'Operação reaberta com sucesso.'})

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro CRÍTICO em /reabrir_operacao para ID {id_ordem_operacao}: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Erro interno no servidor ao reabrir operação.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)           
            
@app.route('/consulta_ordens', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/consulta_ordens')
def consulta_ordens():
    conn_local = None
    ordens = []
    status_list = []
    
    # Parâmetros de Paginação
    page = request.args.get('page', 1, type=int)
    per_page = 20
    offset = (page - 1) * per_page

    # Captura filtros via GET (preferencial para paginação) ou POST
    filtros = {
        "data_inicio": request.args.get("data_inicio", ""),
        "data_fim": request.args.get("data_fim", ""),
        "id_status": request.args.get("id_status", ""),
        "codigo_ordem": request.args.get("codigo_ordem", "")
    }

    # Se for POST, sobrescreve (caso venha do formulário antigo, mas o ideal é o form ser GET)
    if request.method == 'POST':
        filtros["data_inicio"] = request.form.get("data_inicio", "")
        filtros["data_fim"] = request.form.get("data_fim", "")
        filtros["id_status"] = request.form.get("id_status", "")
        filtros["codigo_ordem"] = request.form.get("codigo_ordem", "")

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("SELECT IDStatus, NomeStatus FROM TBL_StatusOrdemProducao ORDER BY NomeStatus")
        status_list = cursor_local.fetchall()

        # Construção da Cláusula WHERE Dinâmica
        where_clause = " WHERE 1=1 "
        params_base = []

        if filtros['data_inicio']:
            try:
                data_inicio_obj = datetime.strptime(filtros['data_inicio'], '%Y-%m-%d').date()
                where_clause += " AND O.DataInicioPlanejada >= ?"
                params_base.append(data_inicio_obj)
            except ValueError:
                flash(f"Data Início inválida.", "warning")

        if filtros['data_fim']:
            try:
                data_fim_obj = datetime.strptime(filtros['data_fim'], '%Y-%m-%d').date()
                where_clause += " AND O.DataFimPlanejada <= ?"
                params_base.append(data_fim_obj)
            except ValueError:
                flash(f"Data Fim inválida.", "warning")

        if filtros['id_status']:
            where_clause += " AND O.IDStatus = ?"
            params_base.append(filtros['id_status'])
        
        if filtros['codigo_ordem']:
            where_clause += " AND O.CodigoOrdem LIKE ?"
            params_base.append(f"%{filtros['codigo_ordem']}%")

        # --- 1. Query para CONTAR total de registros ---
        query_count = f"SELECT COUNT(*) FROM TBL_OrdemProducao O {where_clause}"
        total_registros = cursor_local.execute(query_count, params_base).fetchval()
        total_pages = math.ceil(total_registros / per_page)

        # --- 2. Query para BUSCAR dados paginados ---
        query_data = f"""
            SELECT 
                O.IDOrdem, O.CodigoOrdem, O.IDProduto, O.QuantidadePlanejada,
                O.DataInicioPlanejada, O.DataFimPlanejada,
                P.NomeProduto,
                ISNULL(S.NomeStatus, 'Status Inválido') AS NomeStatus,
                Recurso.NomeMaquina AS NomeRecursoAlocado
            FROM TBL_OrdemProducao O
            INNER JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
            LEFT JOIN TBL_StatusOrdemProducao S ON O.IDStatus = S.IDStatus
            OUTER APPLY (
                SELECT TOP 1 R.NomeMaquina FROM (
                    SELECT E.IDMaquina, E.DataHoraInicio FROM TBL_ExecucaoOP E
                    WHERE E.IDOrdem = O.IDOrdem AND E.Status IN ('Em Execucao', 'Em Setup')
                    UNION ALL
                    SELECT F.IDMaquina, F.DataInsercao AS DataHoraInicio FROM TBL_FilaOrdem F
                    WHERE F.IDOrdem = O.IDOrdem
                ) AS OrigemRecurso
                JOIN TBL_Recurso R ON OrigemRecurso.IDMaquina = R.IDMaquina
                ORDER BY OrigemRecurso.DataHoraInicio DESC
            ) AS Recurso
            {where_clause}
            ORDER BY O.IDOrdem DESC
            OFFSET ? ROWS FETCH NEXT ? ROWS ONLY
        """
        
        # Adiciona os parâmetros de paginação aos parâmetros da query
        params_data = params_base + [offset, per_page]
        
        cursor_local.execute(query_data, params_data)
        ordens = cursor_local.fetchall()

        return render_template('consulta_ordens.html', 
                               ordens=ordens, 
                               status_list=status_list, 
                               filtros=filtros,
                               current_page=page,
                               total_pages=total_pages)

    except pyodbc.Error as e:
        logger.error(f"Erro de banco de dados em consulta_ordens: {e}", exc_info=True)
        flash("Ocorreu um erro de banco de dados ao realizar a consulta.", "danger")
        return render_template('consulta_ordens.html', ordens=[], status_list=status_list, filtros=filtros, current_page=1, total_pages=1)
    except Exception as e:
        logger.error(f"Erro geral em consulta_ordens: {e}", exc_info=True)
        flash("Ocorreu um erro inesperado ao consultar as ordens.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
@app.route('/buscar_produto')
@login_requerido
def buscar_produto():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        codigo = request.args.get('codigo')
        cursor_local.execute("SELECT IDProduto, NomeProduto FROM TBL_Produto WHERE CodigoProduto = ?", codigo)
        produto = cursor_local.fetchone()
        if produto:
            return jsonify({"id": produto.IDProduto, "nome": produto.NomeProduto})
        else:
            return jsonify({"erro": "Produto não encontrado"}), 404
    except Exception as e:
        logger.error(f"Erro em buscar_produto: {e}", exc_info=True)
        return jsonify({"erro": f"Erro interno: {str(e)}"}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
        
# Função auxiliar para obter ID do motivo de parada (não é rota, mas é chamada por outras)
def get_motivo_parada_id_by_description(description_like, conn_local, cursor_local):
    """
    Obtém o ID de um motivo de parada pela descrição.
    Recebe conn_local e cursor_local.
    """
    try:
        cursor_local.execute("""
            SELECT TOP 1 IDMotivoParada
            FROM TBL_MotivoParada
            WHERE Descricao LIKE ?
        """, description_like)
        row = cursor_local.fetchone()
        return row.IDMotivoParada if row else None
    except Exception as e:
        logger.error(f"Erro em get_motivo_parada_id_by_description: {e}", exc_info=True)
        return None

# --- ROTAS DE DASHBOARD E MONITORAMENTO ---
@app.route('/classificar_parada', methods=['POST'])
@login_requerido
def classificar_parada():
    data = request.get_json()
    id_maquina = data.get('id_maquina')
    id_motivo_parada = data.get('id_motivo_parada')

    if not id_maquina or not id_motivo_parada:
        return jsonify({'success': False, 'message': 'Dados incompletos.'}), 400

    conn = None
    try:
        conn = obter_conexao()
        cursor = conn.cursor()

        # Atualizar o status atual para incluir o motivo da parada
        cursor.execute("""
            UPDATE TBL_StatusMaquina
            SET IDMotivoParada = ?
            WHERE IDMaquina = ? AND DataHoraFim IS NULL AND Status = 0
        """, (id_motivo_parada, id_maquina))

        conn.commit()
        return jsonify({'success': True, 'message': 'Parada classificada com sucesso!'})

    except Exception as e:
        logger.error(f"Erro ao classificar parada: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': f'Erro interno: {str(e)}'}), 500
    finally:
        if conn:
            devolver_conexao(conn)
@app.route('/api/associar-operador', methods=['POST'])
@login_requerido
def associar_operador():
    conn_local = None
    try:
        data = request.get_json()
        id_maquina = data.get('id_maquina')
        id_operador = data.get('id_operador')

        if not id_maquina or not id_operador:
            return jsonify({'success': False, 'message': 'Dados incompletos (ID da máquina ou do operador ausente).'}), 400

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # A associação só pode ser salva se houver uma execução ATIVA.
        cursor_local.execute("""
            SELECT TOP 1 IDExecucao FROM TBL_ExecucaoOP
            WHERE IDMaquina = ? AND Status = 'Em Execucao'
            ORDER BY DataHoraInicio DESC
        """, (id_maquina,))
        execucao_ativa = cursor_local.fetchone()

        if not execucao_ativa:
            logger.warning(f"Tentativa de associar operador {id_operador} à máquina {id_maquina} sem uma OP ativa. A associação não pode ser salva.")
            # Informa ao usuário que a ação não pode ser concluída.
            return jsonify({'success': False, 'message': 'Ação não permitida: Associe um operador apenas em máquinas com Ordem de Produção em execução.'}), 400

        # Se encontrou uma execução ativa, atualiza o operador.
        cursor_local.execute("""
            UPDATE TBL_ExecucaoOP SET IDOperador = ? WHERE IDExecucao = ?
        """, (id_operador, execucao_ativa.IDExecucao))
        conn_local.commit()
        
        logger.info(f"Operador ID {id_operador} associado à execução {execucao_ativa.IDExecucao} na máquina {id_maquina}.")
        return jsonify({'success': True, 'message': 'Operador associado com sucesso!'})

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao associar operador: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Ocorreu um erro interno no servidor.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)            

def obter_disponibilidade_turno(id_maquina, id_turno):
    """
    [VERSÃO FINAL COM FALLBACK PARA LIMITE DE SETUP]
    Calcula a disponibilidade, tratando o tempo excedente de paradas de setup
    e outras paradas planejadas como tempo de parada não planejado.
    Prioriza limite de TBL_RecursoProduto > TBL_OrdemProducao_Operacoes > TBL_MotivoParada.
    """
    conn_local = None
    try:
        # conn_local = conectar_bd() # Usa conexão local para evitar conflito de pool na chamada original
        # Correção: Melhor obter do pool, mas gerenciar cuidadosamente
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()


        if not id_turno:
            # logger.warning(f"obter_disponibilidade_turno chamado sem id_turno para máquina {id_maquina}.") # Log Opcional
            return {'TempoRodando': 0, 'TempoParado': 0, 'Disponibilidade_Pct': 0.0}

        # Busca limites genéricos das paradas planejadas (incluindo setup)
        cursor_local.execute("SELECT IDMotivoParada, TempoLimiteMinutos FROM TBL_MotivoParada WHERE FlgPlanejada = 1")
        paradas_planejadas_com_limite = {row.IDMotivoParada: row.TempoLimiteMinutos for row in cursor_local.fetchall()}
        ids_paradas_planejadas = set(paradas_planejadas_com_limite.keys())

        # Identifica o ID do motivo de setup
        cursor_local.execute("SELECT IDMotivoParada FROM TBL_MotivoParada WHERE Codigo = '03'") # Confirme se '03' é o código correto
        motivo_setup_row = cursor_local.fetchone()
        id_motivo_setup = motivo_setup_row.IDMotivoParada if motivo_setup_row else -1
        # logger.debug(f"ID Motivo Setup identificado: {id_motivo_setup}") # Log Opcional

        # Busca horários do turno
        cursor_local.execute("SELECT HoraInicio, HoraFim FROM TBL_Turno WHERE IDTurno = ?", id_turno)
        row_turno = cursor_local.fetchone()
        if not row_turno:
            logger.error(f"Turno ID {id_turno} não encontrado no banco.")
            return {'TempoRodando': 0, 'TempoParado': 0, 'Disponibilidade_Pct': 0.0}

        # Calcula o período de análise dentro do turno
        agora = datetime.now()
        inicio_turno = datetime.combine(agora.date(), row_turno.HoraInicio)
        fim_turno = datetime.combine(agora.date(), row_turno.HoraFim)

        if row_turno.HoraFim < row_turno.HoraInicio: # Turno que vira a noite
            if agora.time() <= row_turno.HoraFim: # Se já virou a noite
                inicio_turno -= timedelta(days=1)
            else: # Se ainda não virou a noite
                fim_turno += timedelta(days=1)

        fim_periodo_analise = min(agora, fim_turno) # Não calcula além do fim do turno ou do momento atual
        # Garante que o período de análise seja válido
        if fim_periodo_analise <= inicio_turno:
             # logger.debug(f"Período de análise inválido ou turno ainda não iniciado para máq {id_maquina}. Início: {inicio_turno}, Fim Análise: {fim_periodo_analise}") # Log Opcional
             return {'TempoRodando': 0, 'TempoParado': 0, 'Disponibilidade_Pct': 0.0}

        tempo_total_decorrido_seg = (fim_periodo_analise - inicio_turno).total_seconds()
        if tempo_total_decorrido_seg <= 0:
             return {'TempoRodando': 0, 'TempoParado': 0, 'Disponibilidade_Pct': 0.0}

        # Busca registros de status relevantes para o período
        # logger.debug(f"Buscando status para Máq {id_maquina} entre {inicio_turno} e {fim_periodo_analise}") # Log Opcional
        cursor_local.execute("""
            SELECT sm.Status, sm.DataHoraInicio, ISNULL(sm.DataHoraFim, ?) AS DataHoraFimCalculada, sm.IDMotivoParada
            FROM TBL_StatusMaquina sm WITH (NOLOCK)
            WHERE sm.IDMaquina = ?
              AND sm.DataHoraInicio < ? -- Status que começou antes do fim da análise
              AND ISNULL(sm.DataHoraFim, ?) > ? -- Status que terminou (ou está ativo) depois do início do turno
            ORDER BY sm.DataHoraInicio
        """, (agora, id_maquina, fim_periodo_analise, agora, inicio_turno)) # Usa agora como fallback para DataHoraFim NULL

        registros_status = cursor_local.fetchall()
        # logger.debug(f"Encontrados {len(registros_status)} registros de status para Máq {id_maquina} no período.") # Log Opcional

        tempo_rodando_segundos = 0
        tempo_parado_nao_planejado_segundos = 0
        tempo_parado_planejado_segundos = 0

        for registro in registros_status:
            # Ajusta início e fim do evento para estarem DENTRO do período de análise do turno
            inicio_evento = max(registro.DataHoraInicio, inicio_turno)
            fim_evento = min(registro.DataHoraFimCalculada, fim_periodo_analise)
            duracao_segundos_real = (fim_evento - inicio_evento).total_seconds()

            if duracao_segundos_real <= 0: continue # Ignora durações inválidas ou zero

            if registro.Status == 1: # Produzindo
                tempo_rodando_segundos += duracao_segundos_real
            else: # Parado
                tempo_limite_planejado_segundos = 0 # Reseta o limite para cada parada

                # --- LÓGICA DE BUSCA DO LIMITE (com Fallback) ---
                if registro.IDMotivoParada == id_motivo_setup:
                    # 1. Tenta buscar em TBL_RecursoProduto (prioridade)
                    try:
                        # Tenta encontrar a execução (pode ser 'Em Setup' ou 'Em Execucao') ligada a este momento
                        cursor_local.execute("""
                            SELECT TOP 1 RP.TempoSetupSegundos, EX.IDOrdemOperacao
                            FROM TBL_ExecucaoOP EX WITH (NOLOCK)
                            JOIN TBL_OrdemProducao OP WITH (NOLOCK) ON EX.IDOrdem = OP.IDOrdem
                            JOIN TBL_RecursoProduto RP WITH (NOLOCK) ON EX.IDMaquina = RP.IDRecurso AND OP.IDProduto = RP.IDProduto
                            WHERE EX.IDMaquina = ?
                              AND ? >= EX.DataHoraInicio -- O início do status é durante ou após o início da execução
                              AND (EX.DataHoraFim IS NULL OR ? < EX.DataHoraFim) -- O início do status é antes do fim da execução (ou ela está ativa)
                              AND RP.TempoSetupSegundos IS NOT NULL
                            ORDER BY EX.DataHoraInicio DESC -- Pega a execução mais recente que cobre o período
                        """, (id_maquina, registro.DataHoraInicio, registro.DataHoraInicio))
                        setup_config_rp = cursor_local.fetchone()
                        if setup_config_rp:
                            tempo_limite_planejado_segundos = float(setup_config_rp.TempoSetupSegundos)
                            id_ordem_operacao_contexto = setup_config_rp.IDOrdemOperacao # Guarda para fallback 2
                            # logger.debug(f"Setup Máq {id_maquina}: Limite encontrado em RecursoProduto: {tempo_limite_planejado_segundos}s") # Log Opcional
                        else:
                             # 2. Fallback: Tenta buscar em TBL_OrdemProducao_Operacoes
                             #    Precisamos do IDOrdemOperacao da execução ativa naquele momento
                             cursor_local.execute("""
                                SELECT TOP 1 EX.IDOrdemOperacao
                                FROM TBL_ExecucaoOP EX WITH (NOLOCK)
                                WHERE EX.IDMaquina = ?
                                  AND ? >= EX.DataHoraInicio
                                  AND (EX.DataHoraFim IS NULL OR ? < EX.DataHoraFim)
                                ORDER BY EX.DataHoraInicio DESC
                             """, (id_maquina, registro.DataHoraInicio, registro.DataHoraInicio))
                             exec_contexto = cursor_local.fetchone()
                             if exec_contexto and exec_contexto.IDOrdemOperacao:
                                 cursor_local.execute("""
                                    SELECT TempoSetupPlanejadoMinutos
                                    FROM TBL_OrdemProducao_Operacoes WITH (NOLOCK)
                                    WHERE IDOrdemOperacao = ? AND TempoSetupPlanejadoMinutos IS NOT NULL
                                 """, (exec_contexto.IDOrdemOperacao,))
                                 setup_config_op = cursor_local.fetchone()
                                 if setup_config_op:
                                     tempo_limite_planejado_segundos = float(setup_config_op.TempoSetupPlanejadoMinutos) * 60
                                     # logger.debug(f"Setup Máq {id_maquina}: Limite encontrado em OrdemOperacao: {tempo_limite_planejado_segundos}s") # Log Opcional
                                 else:
                                      # 3. Fallback Final: Usa limite genérico de TBL_MotivoParada
                                      tempo_limite_minutos_generico = paradas_planejadas_com_limite.get(id_motivo_setup)
                                      if tempo_limite_minutos_generico and tempo_limite_minutos_generico > 0:
                                          tempo_limite_planejado_segundos = tempo_limite_minutos_generico * 60
                                          # logger.debug(f"Setup Máq {id_maquina}: Usando limite genérico de MotivoParada: {tempo_limite_planejado_segundos}s") # Log Opcional
                    except Exception as e_setup_limit:
                        logger.error(f"Erro ao buscar limite de setup para Máq {id_maquina}: {e_setup_limit}")
                        # Se der erro na busca, tenta o limite genérico como segurança
                        tempo_limite_minutos_generico = paradas_planejadas_com_limite.get(id_motivo_setup)
                        if tempo_limite_minutos_generico and tempo_limite_minutos_generico > 0:
                            tempo_limite_planejado_segundos = tempo_limite_minutos_generico * 60

                elif registro.IDMotivoParada in ids_paradas_planejadas:
                    # Para outras paradas planejadas, usa o limite genérico
                    tempo_limite_minutos = paradas_planejadas_com_limite.get(registro.IDMotivoParada)
                    if tempo_limite_minutos and tempo_limite_minutos > 0:
                        tempo_limite_planejado_segundos = tempo_limite_minutos * 60
                        # logger.debug(f"Parada Plan. Máq {id_maquina} (Motivo {registro.IDMotivoParada}): Limite genérico: {tempo_limite_planejado_segundos}s") # Log Opcional
                # --- FIM DA LÓGICA DE BUSCA DO LIMITE ---

                # --- Aplica o limite encontrado (se houver) ---
                if tempo_limite_planejado_segundos and tempo_limite_planejado_segundos > 0:
                    parte_planejada = min(duracao_segundos_real, tempo_limite_planejado_segundos)
                    parte_nao_planejada = max(0, duracao_segundos_real - tempo_limite_planejado_segundos)

                    tempo_parado_planejado_segundos += parte_planejada
                    tempo_parado_nao_planejado_segundos += parte_nao_planejada # Tempo excedente penaliza
                    # logger.debug(f"Parada Plan. Máq {id_maquina}: Duração={duracao_segundos_real}s, Limite={tempo_limite_planejado_segundos}s => Plan={parte_planejada}s, NPlan={parte_nao_planejada}s") # Log Opcional
                else:
                    # Se não encontrou limite ou não é planejada, conta tudo como não planejado
                    tempo_parado_nao_planejado_segundos += duracao_segundos_real
                    # logger.debug(f"Parada NPlan Máq {id_maquina} (Motivo {registro.IDMotivoParada}): Duração={duracao_segundos_real}s => NPlan={duracao_segundos_real}s") # Log Opcional

        # --- Cálculo Final da Disponibilidade ---
        tempo_total_disponivel_planejado_seg = tempo_total_decorrido_seg - tempo_parado_planejado_segundos # Subtrai APENAS o tempo planejado DENTRO do limite

        if tempo_total_disponivel_planejado_seg <= 0: # Evita divisão por zero ou negativo
             disponibilidade_pct = 0.0
        else:
             disponibilidade_pct = (tempo_rodando_segundos / tempo_total_disponivel_planejado_seg) * 100

        # logger.debug(f"Cálculo Disp. Máq {id_maquina}: Total={tempo_total_decorrido_seg}s, Rodando={tempo_rodando_segundos}s, ParadoPlan={tempo_parado_planejado_segundos}s, ParadoNPlan={tempo_parado_nao_planejado_segundos}s => Disponível={tempo_total_disponivel_planejado_seg}s => Disp%={disponibilidade_pct:.2f}%") # Log Opcional

        return {
            'TempoRodando': int(round(tempo_rodando_segundos)),
            'TempoParado': int(round(tempo_parado_nao_planejado_segundos)), # Retorna apenas o não planejado (inclui excedente)
            'Disponibilidade_Pct': round(disponibilidade_pct, 2)
        }

    except Exception as e:
        logger.error(f"Erro CRÍTICO ao calcular disponibilidade para máquina {id_maquina}: {str(e)}", exc_info=True)
        return {'TempoRodando': 0, 'TempoParado': 0, 'Disponibilidade_Pct': 0.0}
    finally:
        if conn_local:
            devolver_conexao(conn_local) # Devolve a conexão ao pool
            
###########################################################################DASHBOARD##################################################################################

            
def _get_dashboard_data_optimized(setor_selecionado, recurso_selecionado):
    """
    [VERSÃO OTIMIZADA - PERFORMANCE + CICLO REAL RECENTE]
    - Lê diretamente de TBL_EventoProducao.
    - Calcula Ciclo Real baseado na média dos últimos 20 pulsos.
    """
    recursos = []
    conn_local = None
    logger.info(f"Iniciando dashboard otimizado (TBL_EventoProducao + Ciclo 20 ultimos) com filtros: {setor_selecionado}, {recurso_selecionado}")
    
    # Query Principal
    sql_principal_consolidado_final = """
    WITH StatusAtual AS (
        SELECT
            IDMaquina, Status, DataHoraInicio, IDMotivoParada, ObsEvento,
            ROW_NUMBER() OVER(PARTITION BY IDMaquina ORDER BY DataHoraRegistro DESC) as rn
        FROM TBL_StatusMaquina WHERE DataHoraFim IS NULL
    ),
    ExecucaoAtiva AS (
        SELECT
            ExecOP.IDExecucao, ExecOP.IDMaquina, ExecOP.IDOrdemOperacao,
            ExecOP.IDOperador, Opr.NomeOperador, ExecOP.DataHoraInicio AS DataHoraInicioExecucao,
            OP.IDOrdem, OP.CodigoOrdem, 
            ISNULL(OPO.QuantidadePlanejada, OP.QuantidadePlanejada) AS QuantidadePlanejada, 
            OP.UsarTempoCicloRecurso, OP.DataInicioPlanejada, OP.DataFimPlanejada,
            Prod.IDProduto, Prod.CodigoProduto, Prod.NomeProduto, Prod.UnidadesPorCaixa, Prod.NomeDocumentoTecnico,
            OPO.NumeroOperacao, OPO.Descricao AS DescricaoOperacao, OPO.NomeDocumentoTecnico AS DocumentoOperacao,
            OPO.TempoSetupPlanejadoMinutos, UM.NomeUnidade AS UnidadeMedidaProduto,
            CASE WHEN OP.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.TempoCicloPadraoSegundos ELSE Prod.TempoCicloSegundos END AS TempoCicloFinal,
            CASE WHEN OP.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.FatorMultiplicacao ELSE Prod.FatorMultiplicacao END AS FatorMultiplicacaoFinal,
            CASE WHEN OP.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.TempoCiclo ELSE Prod.TempoCicloSegundos END AS TempoCicloOriginal,
            CASE WHEN OP.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.UnidadeTempoCiclo ELSE Prod.UnidadeCiclo COLLATE DATABASE_DEFAULT END AS UnidadeDisplayProduto,
            RP.TempoSetupSegundos AS TempoSetupRecursoProduto,
            ROW_NUMBER() OVER(PARTITION BY ExecOP.IDMaquina ORDER BY ExecOP.DataHoraInicio DESC) as rn_exec
        FROM TBL_ExecucaoOP ExecOP 
        JOIN TBL_OrdemProducao OP  ON ExecOP.IDOrdem = OP.IDOrdem
        JOIN TBL_Produto Prod  ON OP.IDProduto = Prod.IDProduto
        LEFT JOIN TBL_OrdemProducao_Operacoes OPO  ON ExecOP.IDOrdemOperacao = OPO.IDOrdemOperacao
        LEFT JOIN TBL_UnidadeMedida UM  ON Prod.IDUnidade = UM.IDUnidade
        LEFT JOIN TBL_Operador Opr  ON ExecOP.IDOperador = Opr.IDOperador
        LEFT JOIN TBL_RecursoProduto RP  ON ExecOP.IDMaquina = RP.IDRecurso AND Prod.IDProduto = RP.IDProduto
        WHERE ExecOP.Status IN ('Em Execucao', 'Em Setup')
    ),
    TurnoAtualMaquina AS (
        SELECT
            rt.IDRecurso AS IDMaquina, t.IDTurno, t.NomeTurno,
            ROW_NUMBER() OVER (
                PARTITION BY rt.IDRecurso 
                ORDER BY 
                    CASE 
                        WHEN (t.Todos = 1 OR (CASE DATENAME(WEEKDAY, DATEADD(day, -1, GETDATE())) WHEN 'Monday' THEN t.Seg WHEN 'Segunda-feira' THEN t.Seg WHEN 'Tuesday' THEN t.Ter WHEN 'Terça-feira' THEN t.Ter WHEN 'Wednesday' THEN t.Qua WHEN 'Quarta-feira' THEN t.Qua WHEN 'Thursday' THEN t.Qui WHEN 'Quinta-feira' THEN t.Qui WHEN 'Friday' THEN t.Sex WHEN 'Sexta-feira' THEN t.Sex WHEN 'Saturday' THEN t.Sab WHEN 'Sábado' THEN t.Sab WHEN 'Sunday' THEN t.Dom WHEN 'Domingo' THEN t.Dom END) = 1) AND t.IniciaDiaAnterior = 1 AND CAST(GETDATE() AS TIME) <= t.HoraFim THEN 1
                        ELSE 2
                    END ASC, CAST(t.HoraInicio AS TIME) DESC
            ) as rn
        FROM TBL_RecursoTurno rt JOIN TBL_Turno t ON t.IDTurno = rt.IDTurno
        WHERE t.Ativo = 1
          AND (
              ((t.Todos = 1 OR (CASE DATENAME(WEEKDAY, GETDATE()) WHEN 'Monday' THEN t.Seg WHEN 'Segunda-feira' THEN t.Seg WHEN 'Tuesday' THEN t.Ter WHEN 'Terça-feira' THEN t.Ter WHEN 'Wednesday' THEN t.Qua WHEN 'Quarta-feira' THEN t.Qua WHEN 'Thursday' THEN t.Qui WHEN 'Quinta-feira' THEN t.Qui WHEN 'Friday' THEN t.Sex WHEN 'Sexta-feira' THEN t.Sex WHEN 'Saturday' THEN t.Sab WHEN 'Sábado' THEN t.Sab WHEN 'Sunday' THEN t.Dom WHEN 'Domingo' THEN t.Dom END) = 1) AND t.IniciaDiaAnterior = 0 AND CAST(GETDATE() AS TIME) BETWEEN t.HoraInicio AND t.HoraFim)
              OR
              ((t.Todos = 1 OR (CASE DATENAME(WEEKDAY, GETDATE()) WHEN 'Monday' THEN t.Seg WHEN 'Segunda-feira' THEN t.Seg WHEN 'Tuesday' THEN t.Ter WHEN 'Terça-feira' THEN t.Ter WHEN 'Wednesday' THEN t.Qua WHEN 'Quarta-feira' THEN t.Qua WHEN 'Thursday' THEN t.Qui WHEN 'Quinta-feira' THEN t.Qui WHEN 'Friday' THEN t.Sex WHEN 'Sexta-feira' THEN t.Sex WHEN 'Saturday' THEN t.Sab WHEN 'Sábado' THEN t.Sab WHEN 'Sunday' THEN t.Dom WHEN 'Domingo' THEN t.Dom END) = 1) AND t.IniciaDiaAnterior = 1 AND CAST(GETDATE() AS TIME) >= t.HoraInicio)
              OR
              ((t.Todos = 1 OR (CASE DATENAME(WEEKDAY, DATEADD(day, -1, GETDATE())) WHEN 'Monday' THEN t.Seg WHEN 'Segunda-feira' THEN t.Seg WHEN 'Tuesday' THEN t.Ter WHEN 'Terça-feira' THEN t.Ter WHEN 'Wednesday' THEN t.Qua WHEN 'Quarta-feira' THEN t.Qua WHEN 'Thursday' THEN t.Qui WHEN 'Quinta-feira' THEN t.Qui WHEN 'Friday' THEN t.Sex WHEN 'Sexta-feira' THEN t.Sex WHEN 'Saturday' THEN t.Sab WHEN 'Sábado' THEN t.Sab WHEN 'Sunday' THEN t.Dom WHEN 'Domingo' THEN t.Dom END) = 1) AND t.IniciaDiaAnterior = 1 AND CAST(GETDATE() AS TIME) <= t.HoraFim)
          )
    ),
    UltimoOEE_Calculado AS (
        SELECT oee.IDMaquina, oee.IDTurno, oee.Disponibilidade, oee.Performance, oee.Qualidade, oee.OEE,
            ROW_NUMBER() OVER(PARTITION BY oee.IDMaquina, oee.IDTurno ORDER BY oee.DataHoraCalculo DESC) as rn_oee
        FROM TBL_IndiceOEE oee WITH (NOLOCK)
        WHERE oee.DataHoraCalculo >= DATEADD(hour, -24, GETDATE())
    )
    SELECT
        R.IDMaquina, R.NomeMaquina, R.CodigoInterno, S.Nome AS NomeSetor,
        R.MetaOEE, R.MetaQualidade, R.MetaDisponibilidade, R.MetaPerformance, R.UnidadeVelocidadePadrao,
        R.Automatico, R.IdSegmento, R.LinkExterno, SegMaq.NomeSegmento,
        ExecInfo.IDExecucao, ExecInfo.IDOrdemOperacao, ExecInfo.IDOperador, ExecInfo.NomeOperador, ExecInfo.DataHoraInicioExecucao,
        ExecInfo.IDOrdem, ExecInfo.CodigoOrdem, ExecInfo.QuantidadePlanejada, ExecInfo.UsarTempoCicloRecurso,
        ExecInfo.DataInicioPlanejada, ExecInfo.DataFimPlanejada,
        ExecInfo.IDProduto, ExecInfo.CodigoProduto, ExecInfo.NomeProduto, ExecInfo.UnidadesPorCaixa, ExecInfo.NomeDocumentoTecnico,
        ExecInfo.NumeroOperacao, ExecInfo.DescricaoOperacao, ExecInfo.UnidadeMedidaProduto, ExecInfo.DocumentoOperacao,
        ExecInfo.TempoCicloFinal, ExecInfo.FatorMultiplicacaoFinal, ExecInfo.TempoCicloOriginal, ExecInfo.UnidadeDisplayProduto,
        StatusInfo.Status AS StatusAtual, StatusInfo.DataHoraInicio AS DataHoraInicioStatus,
        StatusInfo.IDMotivoParada, 
        StatusInfo.ObsEvento, 
        ISNULL(MP_Status.Descricao, StatusInfo.ObsEvento) AS DescricaoMotivoParada,
        
        ISNULL(ProducaoOperacao.QtdLiquidaOperacao, 0) AS QuantidadeProduzidaOperacao,
        ISNULL(ProducaoOperacao.QtdRefugoOperacao, 0) AS QuantidadeRefugadaOperacao,
        ISNULL(ProducaoOrdemTotal.QtdLiquidaOrdemTotal, 0) AS QtdTotalProduzidaOrdemLiquida,
        ISNULL(TempoRodandoExec.TempoRodandoSegundosExecucao, 0) AS TempoRodandoSegundosExecucao,
        ISNULL(PulsosExecucao.TotalPulsosExecucao, 0) AS TotalPulsosExecucao,
        
        -- >>> CAMPO NOVO: Média dos últimos 20 ciclos <<<
        ISNULL(CicloRealRecente.MediaUltimos20Ciclos, 0) AS MediaUltimos20Ciclos,
        
        ISNULL(ParadasPendentes.Contagem, 0) AS ContagemParadasPendentes,
        ISNULL(AlertasAtivosInfo.ContagemAlertasAtivos, 0) AS ContagemAlertasAtivos,
        ISNULL(TurnoMaq.NomeTurno, 'Fora de Turno') AS NomeTurnoCalculado,
        
        ISNULL(OEE_Calc.Disponibilidade, 0) * 100 AS DisponibilidadeCalculada,
        ISNULL(OEE_Calc.Performance, 0) * 100 AS PerformanceCalculada,
        ISNULL(OEE_Calc.Qualidade, 0) * 100 AS QualidadeCalculada
        
    FROM TBL_Recurso R 
    LEFT JOIN TBL_Setor S ON R.IDSetor = S.IDSetor
    LEFT JOIN TBL_SegmentoMaquina SegMaq ON R.IdSegmento = SegMaq.IdSegmento
    LEFT JOIN ExecucaoAtiva ExecInfo ON R.IDMaquina = ExecInfo.IDMaquina AND ExecInfo.rn_exec = 1
    LEFT JOIN StatusAtual StatusInfo ON R.IDMaquina = StatusInfo.IDMaquina AND StatusInfo.rn = 1
    
    LEFT JOIN TBL_MotivoParada MP_Status ON StatusInfo.IDMotivoParada = MP_Status.IDMotivoParada
    
    LEFT JOIN TurnoAtualMaquina TurnoMaq ON R.IDMaquina = TurnoMaq.IDMaquina AND TurnoMaq.rn = 1
    LEFT JOIN UltimoOEE_Calculado OEE_Calc 
        ON R.IDMaquina = OEE_Calc.IDMaquina 
        AND TurnoMaq.IDTurno = OEE_Calc.IDTurno 
        AND OEE_Calc.rn_oee = 1

    -- >>> OTIMIZAÇÃO: Usa TBL_EventoProducao (tabela física) ao invés da VW lenta <<<
    OUTER APPLY (
        SELECT 
            SUM(CASE WHEN ev.TipoValor IN ('BOA', 'ESTORNO') THEN ev.Quantidade ELSE 0 END) as QtdLiquidaOperacao, 
            SUM(CASE WHEN ev.TipoValor = 'REFUGO' THEN ev.Quantidade ELSE 0 END) as QtdRefugoOperacao 
        FROM TBL_EventoProducao ev -- Alterado de VW para TBL
        JOIN TBL_ExecucaoOP ex_op ON ev.IDExecucao = ex_op.IDExecucao 
        WHERE ex_op.IDOrdemOperacao = ExecInfo.IDOrdemOperacao
    ) AS ProducaoOperacao

    OUTER APPLY (
        SELECT SUM(CASE WHEN ev_ord.TipoValor IN ('BOA', 'ESTORNO') THEN ev_ord.Quantidade ELSE 0 END) as QtdLiquidaOrdemTotal 
        FROM TBL_EventoProducao ev_ord -- Alterado de VW para TBL
        WHERE ev_ord.IDOrdemProducao = ExecInfo.IDOrdem
    ) AS ProducaoOrdemTotal

    OUTER APPLY (
        SELECT COUNT(*) as TotalPulsosExecucao 
        FROM TBL_EventoProducao Pulsos -- Alterado de VW para TBL
        WHERE Pulsos.IDExecucao = ExecInfo.IDExecucao AND Pulsos.TipoValor = 'BOA'
    ) AS PulsosExecucao
    
    -- >>> NOVO CÁLCULO DE CICLO REAL (ÚLTIMOS 20 PULSOS) <<<
    OUTER APPLY (
        SELECT AVG(CicloSegundos) as MediaUltimos20Ciclos
        FROM (
            SELECT TOP 20
                DATEDIFF(MILLISECOND, LAG(DataHoraEvento) OVER (ORDER BY DataHoraEvento), DataHoraEvento) / 1000.0 as CicloSegundos
            FROM TBL_EventoProducao
            WHERE IDExecucao = ExecInfo.IDExecucao 
              AND TipoValor = 'BOA'
            ORDER BY DataHoraEvento DESC
        ) AS UltimosCiclos
        WHERE CicloSegundos IS NOT NULL
    ) AS CicloRealRecente
    -- >>> FIM DO NOVO CÁLCULO <<<

    OUTER APPLY (SELECT SUM(DATEDIFF(SECOND, InicioAjustado, FimAjustado)) AS TempoRodandoSegundosExecucao FROM (SELECT CASE WHEN sm_exec.DataHoraInicio > ExecInfo.DataHoraInicioExecucao THEN sm_exec.DataHoraInicio ELSE ExecInfo.DataHoraInicioExecucao END AS InicioAjustado, CASE WHEN ISNULL(sm_exec.DataHoraFim, GETDATE()) < GETDATE() THEN ISNULL(sm_exec.DataHoraFim, GETDATE()) ELSE GETDATE() END AS FimAjustado FROM TBL_StatusMaquina sm_exec WHERE sm_exec.IDMaquina = R.IDMaquina AND sm_exec.Status = 1 AND sm_exec.DataHoraInicio < GETDATE() AND ISNULL(sm_exec.DataHoraFim, GETDATE()) > ExecInfo.DataHoraInicioExecucao) AS IntervalosAjustados WHERE FimAjustado > InicioAjustado) AS TempoRodandoExec
    OUTER APPLY (SELECT COUNT(*) as Contagem FROM TBL_StatusMaquina sp WHERE sp.IDMaquina = R.IDMaquina AND sp.IDMotivoParada = 2 AND sp.DataHoraFim >= DATEADD(minute, -{minutos_classificacao}, GETDATE())) AS ParadasPendentes
    OUTER APPLY (SELECT COUNT(*) as ContagemAlertasAtivos FROM TBL_LogAlarmes la WHERE la.IDMaquina = R.IDMaquina AND la.Status = 'ATIVO') AS AlertasAtivosInfo
    WHERE R.Ativo = 1
    """

    try:
        conn_local = obter_conexao()
        minutos_para_query = 30
        usa_unidades_caixa_local = False
        with conn_local.cursor() as cursor_temp:
             try:
                 tempo_max_config = obter_configuracao('TEMPO_MAXIMO_CLASSIFICACAO_PARADA_MIN', conn_local, cursor_temp)
                 if tempo_max_config and tempo_max_config.isdigit(): minutos_para_query = int(tempo_max_config)
                 if obter_configuracao('USA_UNIDADES_POR_CAIXA', conn_local, cursor_temp) == 'true': usa_unidades_caixa_local = True
             except Exception: pass

        mapa_turnos_maquina = defaultdict(list)
        with conn_local.cursor() as cursor_turnos:
            cursor_turnos.execute("""SELECT RT.IDRecurso, T.* FROM TBL_Turno T JOIN TBL_RecursoTurno RT ON T.IDTurno = RT.IDTurno WHERE T.Ativo = 1""")
            colunas_turno = [column[0] for column in cursor_turnos.description]
            for row in cursor_turnos.fetchall():
                turno_dict = dict(zip(colunas_turno, row))
                if isinstance(turno_dict['HoraInicio'], str): turno_dict['HoraInicio'] = datetime.strptime(turno_dict['HoraInicio'], "%H:%M:%S").time()
                if isinstance(turno_dict['HoraFim'], str): turno_dict['HoraFim'] = datetime.strptime(turno_dict['HoraFim'], "%H:%M:%S").time()
                mapa_turnos_maquina[row.IDRecurso].append(turno_dict)

        sql_formatada = sql_principal_consolidado_final.format(minutos_classificacao=minutos_para_query)
        params = []
        if recurso_selecionado:
            sql_formatada += " AND R.IDMaquina = ?"; params.append(recurso_selecionado)
        elif setor_selecionado:
            sql_formatada += " AND R.IDSetor = ?"; params.append(setor_selecionado)
        sql_formatada += " ORDER BY R.NomeMaquina"
        
        with conn_local.cursor() as cursor_local:
            cursor_local.execute(sql_formatada, params)
            dados_brutos = cursor_local.fetchall()
        
        for i, maquina_data in enumerate(dados_brutos):
            id_maquina = maquina_data.IDMaquina
            nome_turno_maquina = maquina_data.NomeTurnoCalculado
            disponibilidade_pct = 0.0
            performance = 0.0
            qualidade = 0.0
            oee = 0.0
            planejado_label, planejado_valor, planejado_unidade = 'Planejado', 0, '-'
            real_label, real_valor, real_unidade = 'Real', 0, '-'
            quantidade_pendente_operacao_unidades = 0
            quantidade_pendente_operacao_caixas = 0
            progresso_operacao_percentual = 0.0
            qtd_produzida_operacao_liquida = 0.0
            qtd_refugo_operacao = 0.0
            qtd_planejada_ordem = 0.0
            tempo_previsto_str = "00:00:00"
            
            if maquina_data.IDOrdem:
                if nome_turno_maquina != 'Fora de Turno':
                    disponibilidade_pct = float(maquina_data.DisponibilidadeCalculada or 0)
                    performance = float(maquina_data.PerformanceCalculada or 0)
                    qualidade = float(maquina_data.QualidadeCalculada or 0)
                    oee = (disponibilidade_pct / 100.0) * (performance / 100.0) * (qualidade / 100.0) * 100.0
                
                qtd_produzida_operacao_liquida = float(maquina_data.QuantidadeProduzidaOperacao or 0)
                qtd_refugo_operacao = float(maquina_data.QuantidadeRefugadaOperacao or 0)
                qtd_planejada_ordem = float(maquina_data.QuantidadePlanejada or 0)
                quantidade_pendente_operacao_unidades = max(0, qtd_planejada_ordem - qtd_produzida_operacao_liquida)
                
                if usa_unidades_caixa_local and maquina_data.UnidadesPorCaixa and maquina_data.UnidadesPorCaixa > 0:
                     unidades_por_caixa_float = float(maquina_data.UnidadesPorCaixa)
                     quantidade_pendente_operacao_caixas = math.ceil(quantidade_pendente_operacao_unidades / unidades_por_caixa_float)
                
                if qtd_planejada_ordem > 0:
                     progresso_operacao_percentual = (qtd_produzida_operacao_liquida / qtd_planejada_ordem * 100)
                else:
                     progresso_operacao_percentual = 100.0 if qtd_produzida_operacao_liquida > 0 else 0.0
                
                tempo_ciclo_seg = float(maquina_data.TempoCicloFinal or 0)
                fator_multiplicacao = float(maquina_data.FatorMultiplicacaoFinal or 1)
                
                # --- ALTERAÇÃO AQUI: USA O CICLO REAL DOS ÚLTIMOS 20 PULSOS ---
                ciclo_real_medio_por_pulso_seg = float(maquina_data.MediaUltimos20Ciclos or 0)
                # --------------------------------------------------------------
                
                unidade_final_a_usar = maquina_data.UnidadeDisplayProduto
                if maquina_data.UsarTempoCicloRecurso == False and maquina_data.UnidadeVelocidadePadrao:
                     unidade_final_a_usar = maquina_data.UnidadeVelocidadePadrao
                unidade_display = str(unidade_final_a_usar or '').lower()
                
                # Para o cálculo de velocidade (un/min, kg/h), precisamos usar o tempo real médio calculado
                if 'un/' in unidade_display or 'kg/' in unidade_display or 'mt/' in unidade_display:
                    velocidade_planejada_base_min = (60 / tempo_ciclo_seg) * fator_multiplicacao if tempo_ciclo_seg > 0 else 0
                    
                    # Cálculo da velocidade real baseada no ciclo real médio recente
                    if ciclo_real_medio_por_pulso_seg > 0:
                        velocidade_real_media_base_min = (60.0 / ciclo_real_medio_por_pulso_seg) * fator_multiplicacao
                    else:
                        velocidade_real_media_base_min = 0.0

                    fator_conv_map = {'/h': 60.0, '/s': 1.0/60.0}
                    unidade_sufixo = unidade_display.split('/')[-1] if '/' in unidade_display else 'min'
                    fator_conv = fator_conv_map.get(f'/{unidade_sufixo}', 1.0)
                    unidade_prefixo = unidade_display.split('/')[0] if '/' in unidade_display else 'un'
                    
                    planejado_label, planejado_unidade = 'Vel. Planejada', f'{unidade_prefixo}/{unidade_sufixo}'
                    real_label, real_unidade = 'Vel. Real Média', f'{unidade_prefixo}/{unidade_sufixo}'
                    planejado_valor = velocidade_planejada_base_min * fator_conv
                    real_valor = velocidade_real_media_base_min * fator_conv
                else:
                    planejado_label, planejado_valor, planejado_unidade = 'Ciclo Planejado', float(maquina_data.TempoCicloOriginal or 0), unidade_display
                    real_label, real_unidade = 'Ciclo Real Médio', unidade_display
                    fator_conv = 1.0
                    if 'min/' in unidade_display: fator_conv = 1.0 / 60.0
                    elif 'h/' in unidade_display: fator_conv = 1.0 / 3600.0
                    real_valor = ciclo_real_medio_por_pulso_seg * fator_conv

                qtd_restante = quantidade_pendente_operacao_unidades
                segundos_por_unidade_real = 0.0
                if real_valor > 0:
                    if 'un/' in unidade_display or 'kg/' in unidade_display or 'mt/' in unidade_display:
                        divisor_tempo = 3600.0 if '/h' in unidade_display else 60.0
                        segundos_por_unidade_real = divisor_tempo / real_valor
                    else:
                        multiplicador_tempo = 1.0
                        if 'min/' in unidade_display: multiplicador_tempo = 60.0
                        elif 'h/' in unidade_display: multiplicador_tempo = 3600.0
                        tempo_do_ciclo_inteiro_seg = real_valor * multiplicador_tempo
                        if fator_multiplicacao > 0: segundos_por_unidade_real = tempo_do_ciclo_inteiro_seg / fator_multiplicacao
                        else: segundos_por_unidade_real = tempo_do_ciclo_inteiro_seg
                
                if segundos_por_unidade_real <= 0 and tempo_ciclo_seg > 0 and fator_multiplicacao > 0:
                    segundos_por_unidade_real = tempo_ciclo_seg / fator_multiplicacao

                if segundos_por_unidade_real > 0 and qtd_restante > 0:
                    tempo_maquina_ligada_seg = qtd_restante * segundos_por_unidade_real
                    turnos_desta_maquina = mapa_turnos_maquina.get(id_maquina, [])
                    data_fim_real = simular_previsao_termino(tempo_maquina_ligada_seg, turnos_desta_maquina)
                    tempo_total_real_seg = (data_fim_real - datetime.now()).total_seconds()
                    tempo_previsto_str = formatar_segundos_para_hms(tempo_total_real_seg)

            else:
                if maquina_data.StatusAtual == 1: disponibilidade_pct = 100.0
                else: disponibilidade_pct = 0.0
                performance = 0.0
                qualidade = 0.0
                oee = 0.0
                tempo_previsto_str = "00:00:00"
            
            recursos.append({
                'IDMaquina': id_maquina, 'NomeMaquina': maquina_data.NomeMaquina, 'CodigoInterno': maquina_data.CodigoInterno,
                'NomeSetor': maquina_data.NomeSetor, 'StatusAtual': maquina_data.StatusAtual or 0,
                'DataHoraInicioStatus': maquina_data.DataHoraInicioStatus.isoformat() if maquina_data.DataHoraInicioStatus else None,
                'IDMotivoParada': maquina_data.IDMotivoParada, 
                
                'ObsEvento': maquina_data.ObsEvento,
                'DescricaoMotivoParada': maquina_data.DescricaoMotivoParada or maquina_data.ObsEvento or ("Fora de Turno" if nome_turno_maquina == "Fora de Turno" else ("Parada Não Identificada" if maquina_data.StatusAtual == 0 else "Sem Status")),
                
                'IDOperador': maquina_data.IDOperador, 'NomeOperador': maquina_data.NomeOperador,
                'OrdemAtual': maquina_data.CodigoOrdem, 'NumeroOperacao': maquina_data.NumeroOperacao,
                'DescricaoOperacao': maquina_data.DescricaoOperacao, 'QuantidadePlanejada': qtd_planejada_ordem,
                'DataInicio': maquina_data.DataInicioPlanejada, 'DataFim': maquina_data.DataFimPlanejada,
                'CodigoProduto': maquina_data.CodigoProduto, 'NomeProduto': maquina_data.NomeProduto,
                'NomeDocumentoTecnico': maquina_data.NomeDocumentoTecnico, 'DocumentoOperacao': maquina_data.DocumentoOperacao, 
                'unidade_medida': maquina_data.UnidadeMedidaProduto,
                'QuantidadeProduzida': qtd_produzida_operacao_liquida, 'QuantidadeRefugada': qtd_refugo_operacao,
                'UnidadesPorCaixa': maquina_data.UnidadesPorCaixa, 'CaixasProduzidas': (qtd_produzida_operacao_liquida // maquina_data.UnidadesPorCaixa) if maquina_data.UnidadesPorCaixa else 0,
                'OEE': oee, 'Disponibilidade': disponibilidade_pct, 'Performance': performance, 'Qualidade': qualidade,
                'MetaOEE': float(maquina_data.MetaOEE or 85), 'MetaQualidade': float(maquina_data.MetaQualidade or 95),
                'MetaDisponibilidade': float(maquina_data.MetaDisponibilidade or 90), 'MetaPerformance': float(maquina_data.MetaPerformance or 95),
                'PlanejadoLabel': planejado_label, 'PlanejadoValor': planejado_valor, 'PlanejadoUnidade': planejado_unidade,
                'RealLabel': real_label, 'RealValor': real_valor, 'RealUnidade': real_unidade,
                'TurnoAtual': nome_turno_maquina, 'ContagemParadasPendentes': maquina_data.ContagemParadasPendentes,
                'ContagemAlertasAtivos': maquina_data.ContagemAlertasAtivos or 0,
                'QuantidadePendenteUnidades': quantidade_pendente_operacao_unidades,
                'QuantidadePendenteCaixas': quantidade_pendente_operacao_caixas,
                'ProgressoPercentual': progresso_operacao_percentual,
                'Automatico': maquina_data.Automatico, 'IdSegmento': maquina_data.IdSegmento, 'LinkExterno': maquina_data.LinkExterno,
                'TempoPrevistoFinalizar': tempo_previsto_str
            })
        return recursos
    
    except Exception as e:
        logger.error(f"Erro CRÍTICO em _get_dashboard_data_optimized: {e}", exc_info=True)
        if conn_local: devolver_conexao(conn_local)
        return [] 
    finally:
        if conn_local: devolver_conexao(conn_local)
        
def simular_previsao_termino(segundos_restantes, turnos_da_maquina):
    """
    Calcula a data de término pulando os horários em que a fábrica está fechada.
    """
    if not turnos_da_maquina or segundos_restantes <= 0:
        return datetime.now() + timedelta(seconds=segundos_restantes)

    tempo_restante = segundos_restantes
    cursor_tempo = datetime.now()
    limite_dias = 45 # Segurança contra loop infinito
    dias_simulados = 0

    while tempo_restante > 0 and dias_simulados < limite_dias:
        dia_da_semana = cursor_tempo.weekday()
        campos_dias = ['Seg', 'Ter', 'Qua', 'Qui', 'Sex', 'Sab', 'Dom']
        coluna_hoje = campos_dias[dia_da_semana]
        
        intervalos_dia = []
        for t in turnos_da_maquina:
            # Verifica se o turno funciona neste dia
            if t.get(coluna_hoje) or t.get('Todos'):
                inicio = t['HoraInicio']
                fim = t['HoraFim']
                dt_inicio = datetime.combine(cursor_tempo.date(), inicio)
                dt_fim = datetime.combine(cursor_tempo.date(), fim)
                
                if t.get('IniciaDiaAnterior'):
                    # Turno que virou a noite (parte da madrugada e parte da noite)
                    intervalos_dia.append((datetime.combine(cursor_tempo.date(), datetime.min.time()), dt_fim))
                    intervalos_dia.append((dt_inicio, datetime.combine(cursor_tempo.date(), datetime.max.time())))
                elif fim < inicio:
                    # Fallback para virada sem flag
                    intervalos_dia.append((dt_inicio, datetime.combine(cursor_tempo.date(), datetime.max.time())))
                else:
                    # Turno normal
                    intervalos_dia.append((dt_inicio, dt_fim))

        intervalos_dia.sort(key=lambda x: x[0])
        
        for inicio_interv, fim_interv in intervalos_dia:
            if fim_interv <= cursor_tempo: continue
            
            inicio_util = max(inicio_interv, cursor_tempo)
            segundos_disponiveis = (fim_interv - inicio_util).total_seconds()
            
            if segundos_disponiveis > 0:
                if tempo_restante <= segundos_disponiveis:
                    return inicio_util + timedelta(seconds=tempo_restante)
                else:
                    tempo_restante -= segundos_disponiveis
                    cursor_tempo = fim_interv

        # Avança para o próximo dia
        cursor_tempo = datetime.combine(cursor_tempo.date() + timedelta(days=1), datetime.min.time())
        dias_simulados += 1

    return datetime.now() + timedelta(seconds=segundos_restantes)        
        
@app.route('/dashboard')
@login_requerido
@permissao_requerida('/dashboard')
def dashboard():
    conn_local = None
    try:
        setor_selecionado = request.args.get('setor', type=int)
        recurso_selecionado = request.args.get('recurso', type=int)

        conn_local = obter_conexao() 

        minutos_classificacao_config = 30 # Define 30 como padrão

        with conn_local.cursor() as cursor_local:
            usa_unidades_caixa = (obter_configuracao('USA_UNIDADES_POR_CAIXA', conn_local, cursor_local) == 'true')
            
            # Busca a configuração de tempo no banco
            tempo_max_config_db = obter_configuracao('TEMPO_MAXIMO_CLASSIFICACAO_PARADA_MIN', conn_local, cursor_local)
            if tempo_max_config_db and tempo_max_config_db.isdigit():
                minutos_classificacao_config = int(tempo_max_config_db) # Sobrescreve o padrão

            cursor_local.execute("SELECT IDSetor, Nome, Codigo FROM TBL_Setor WHERE Ativo = 1 ORDER BY Nome")
            setores = cursor_local.fetchall()
            query_recursos_filtro = "SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1"
            params_recursos_filtro = []
            if setor_selecionado:
                query_recursos_filtro += " AND IDSetor = ?"
                params_recursos_filtro.append(setor_selecionado)
            query_recursos_filtro += " ORDER BY NomeMaquina"
            cursor_local.execute(query_recursos_filtro, params_recursos_filtro)
            recursos_para_filtro = cursor_local.fetchall()
            cursor_local.execute("""
                SELECT o.IDOperador, o.NomeOperador, u.RegistroFuncional
                FROM TBL_Operador o JOIN TBL_Usuario u ON o.IDUsuario = u.IDUsuario
                WHERE o.Ativo = 1 AND u.Ativo = 1 ORDER BY o.NomeOperador
            """)
            operadores_disponiveis = cursor_local.fetchall()
            cursor_local.execute("SELECT IDMotivoRefugo, Descricao FROM TBL_MotivoRefugo WHERE Ativo = 1")
            motivos_refugo = cursor_local.fetchall()
            cursor_local.execute("SELECT IDMotivoParada, Descricao, Codigo,ComentarioObrigatorio FROM TBL_MotivoParada WHERE Ativo = 1 AND Sistema = 0 ORDER BY Codigo")
            motivos_parada = cursor_local.fetchall()
            
            id_motivo_padrao = ID_MOTIVO_PARADA_AUTOMATICA # Usar a constante global

        # Chama a função OTIMIZADA
        recursos_para_template = _get_dashboard_data_optimized(setor_selecionado, recurso_selecionado)
        
        # Bloco de retorno corrigido (atenção à indentação)
        return render_template('dashboard.html',
                           recursos=recursos_para_template,
                           operadores_disponiveis=operadores_disponiveis,
                           motivos_refugo=motivos_refugo,
                           motivos_parada=motivos_parada,
                           id_motivo_padrao=id_motivo_padrao,
                           turno_atual={'id': None},
                           setores=setores,
                           setor_selecionado=setor_selecionado,
                           usa_unidades_caixa=usa_unidades_caixa,
                           recursos_para_filtro=recursos_para_filtro,
                           recurso_selecionado=recurso_selecionado,
                           tempo_max_classificacao=minutos_classificacao_config
                           )
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/api/dashboard_data')
@login_requerido
def api_dashboard_data():
    conn_local = None # conn_local não é mais necessário aqui se a revalidação for removida
    try:
        setor = request.args.get('setor', type=int)
        recurso = request.args.get('recurso', type=int)

        # === ALTERAÇÃO PRINCIPAL AQUI ===
        # Chama a função OTIMIZADA
        dados_maquinas = _get_dashboard_data_optimized(setor, recurso)
        # === FIM DA ALTERAÇÃO ===

        # REMOVER A REVALIDAÇÃO DE STATUS FEITA AQUI (a query consolidada já deve trazer o status correto)
        # conn_local = obter_conexao()
        # with conn_local.cursor() as cursor_local:
        #     for maquina in dados_maquinas:
        #         cursor_local.execute(...) # <- REMOVER ESTE BLOCO

        # Formatação de data (mantém)
        for maquina in dados_maquinas:
             # Garante que a chave existe antes de tentar formatar
            if 'DataHoraInicioStatus' in maquina and isinstance(maquina.get('DataHoraInicioStatus'), datetime):
                 maquina['DataHoraInicioStatus'] = maquina['DataHoraInicioStatus'].isoformat()
            # Faça o mesmo para outras datas se necessário (DataInicio, DataFim)
            if 'DataInicio' in maquina and isinstance(maquina.get('DataInicio'), datetime):
                 maquina['DataInicio'] = maquina['DataInicio'].date().isoformat() # Apenas data
            if 'DataFim' in maquina and isinstance(maquina.get('DataFim'), datetime):
                 maquina['DataFim'] = maquina['DataFim'].date().isoformat() # Apenas data

        return jsonify(dados_maquinas)

    except Exception as e:
        logger.error(f"Erro na rota /api/dashboard_data (Otimizada): {e}", exc_info=True)
        return jsonify([])
    # finally: # Não precisa mais do finally se conn_local não for usado aqui
    #     if conn_local:
    #         devolver_conexao(conn_local)



@app.route('/verificar_turno')
@login_requerido # Rota para JS, mas boa prática manter segurança
def verificar_turno():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        turno_id = identificar_turno(conn_local, cursor_local)
        
        if turno_id:
            cursor_local.execute("SELECT NomeTurno FROM TBL_Turno WHERE IDTurno = ?", (turno_id,))
            turno_row = cursor_local.fetchone()
            turno_descricao = turno_row.NomeTurno if turno_row else "Desconhecido"
            
            return jsonify({
                'success': True,
                'turno_id': turno_id,
                'turno_descricao': turno_descricao
            })
        
        return jsonify({
            'success': True,
            'turno_id': None,
            'message': 'Nenhum turno ativo no momento'
        })
        
    except Exception as e:
        logger.error(f"Erro ao verificar turno atual: {str(e)}", exc_info=True)
        return jsonify({
            'success': False,
            'message': str(e)
        })    
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/heartbeat')
def heartbeat():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        cursor_local.execute("SELECT 1")
        cursor_local.fetchone()
        return jsonify({'status': 'ok', 'timestamp': datetime.now().isoformat()})
    except Exception as e:
        logger.error(f"Erro no heartbeat: {str(e)}", exc_info=True)
        return jsonify({'status': 'error', 'message': str(e)}), 500        
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# Em planner_app.py, substitua esta função inteira:

@app.route('/velocidade_atual/<int:id_maquina>')
@login_requerido
def velocidade_atual(id_maquina):
    conn_local = None
    try:
        conn_local = obter_conexao()
        execucao_ativa = None
        unidade_display = 'un/min' # Default
        label = 'Velocidade Atual' # Default
        valor_final = 0.0
        
        # 1. Busca a execução ativa e a UNIDADE DE DISPLAY configurada/preferida
        with conn_local.cursor() as cursor_local_1:
            cursor_local_1.execute("""
                SELECT TOP 1
                    E.IDExecucao,
                    O.IDProduto,
                    O.UsarTempoCicloRecurso,
                    R.UnidadeVelocidadePadrao,
                    CASE
                        WHEN O.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.UnidadeTempoCiclo
                        ELSE P.UnidadeCiclo -- Usa a unidade do produto como fallback
                    END AS UnidadeDisplayFinal
                FROM TBL_ExecucaoOP E
                JOIN TBL_OrdemProducao O ON E.IDOrdem = O.IDOrdem
                JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
                JOIN TBL_Recurso R ON E.IDMaquina = R.IDMaquina
                LEFT JOIN TBL_RecursoProduto RP ON E.IDMaquina = RP.IDRecurso AND O.IDProduto = RP.IDProduto
                WHERE E.IDMaquina = ? AND E.Status = 'Em Execucao'
                ORDER BY E.DataHoraInicio DESC
            """, (id_maquina,))
            execucao_ativa = cursor_local_1.fetchone()

        if not execucao_ativa:
            # Se não há OP ativa, retorna 0 com unidade padrão
            devolver_conexao(conn_local)
            conn_local = None
            return jsonify({'success': True, 'label': label, 'valor': 0, 'unidade': unidade_display})

        # Define a unidade de display com base na configuração encontrada
        unidade_display = str(execucao_ativa.UnidadeDisplayFinal or '').lower()
        # Se UsarTempoCicloRecurso for falso E existe UnidadeVelocidadePadrao no recurso, usa ela.
        if execucao_ativa.UsarTempoCicloRecurso == False and execucao_ativa.UnidadeVelocidadePadrao:
            unidade_display = str(execucao_ativa.UnidadeVelocidadePadrao or '').lower()


        # 2. Verifica se a unidade de display é baseada em VELOCIDADE ou TEMPO POR PEÇA
        is_speed_unit = 'un/' in unidade_display or 'kg/' in unidade_display or 'mt/' in unidade_display

        # 3. Calcula o ÚLTIMO CICLO REAL em segundos
        ultimo_ciclo_real_segundos = 0.0
        with conn_local.cursor() as cursor_local_2:
            # Query para buscar o tempo em milissegundos entre os dois últimos pulsos 'BOA' da execução atual
            query_ultimo_ciclo = """
                WITH UltimosEventos AS (
                    SELECT TOP 2
                        DataHoraEvento
                    FROM VW_EventoProducaoComCicloReal
                    WHERE IDExecucao = ? AND TipoValor = 'BOA' AND IDMaquina = ?
                    ORDER BY DataHoraEvento DESC
                )
                SELECT CAST(DATEDIFF(MILLISECOND, MIN(DataHoraEvento), MAX(DataHoraEvento)) AS FLOAT) / 1000.0 as UltimoCicloSegundos
                FROM UltimosEventos
                HAVING COUNT(*) = 2; -- Garante que pegamos dois eventos para calcular a diferença
            """
            cursor_local_2.execute(query_ultimo_ciclo, (execucao_ativa.IDExecucao, id_maquina))
            resultado_ciclo = cursor_local_2.fetchone()
            if resultado_ciclo and resultado_ciclo.UltimoCicloSegundos is not None:
                ultimo_ciclo_real_segundos = float(resultado_ciclo.UltimoCicloSegundos)

        # 4. Determina o valor final e o label com base na unidade de display
        unidade_final = unidade_display # Por padrão
        
        if is_speed_unit:
            label = 'Velocidade Atual'
            velocidade_base_min = (60.0 / ultimo_ciclo_real_segundos) if ultimo_ciclo_real_segundos > 0 else 0.0

            unidade_sufixo = unidade_display.split('/')[-1]
            unidade_prefixo = unidade_display.split('/')[0]
            unidade_final = f'{unidade_prefixo}/{unidade_sufixo}'

            fator_conversao = 1.0
            if 'h' in unidade_sufixo: fator_conversao = 60.0
            elif 's' in unidade_sufixo: fator_conversao = 1.0 / 60.0

            valor_final = velocidade_base_min * fator_conversao
            # Arredonda para inteiro se for unidade por tempo
            if '/min' in unidade_final or '/h' in unidade_final or '/s' in unidade_final:
                 valor_final = round(valor_final)
            else: # Mantém decimais para outras unidades (kg/h, mt/min)
                 valor_final = round(valor_final, 2)

        else: # Unidade é tempo por peça (s/un, min/un, etc.)
            label = 'Ciclo Atual'
            fator_conversao = 1.0
            if 'min/' in unidade_display: fator_conversao = 1.0 / 60.0
            elif 'h/' in unidade_display: fator_conversao = 1.0 / 3600.0

            valor_final = ultimo_ciclo_real_segundos * fator_conversao
            valor_final = round(valor_final, 2) # Mantém 2 casas decimais para ciclo

        return jsonify({
            'success': True,
            'label': label,
            'valor': valor_final,
            'unidade': unidade_final
        })

    except Exception as e:
        logger.error(f"Erro ao obter velocidade/ciclo atual para máquina {id_maquina}: {e}", exc_info=True)
        # Retorna um valor padrão em caso de erro, mas indica falha
        return jsonify({'success': False, 'label': 'Erro', 'valor': 0, 'unidade': 'N/A'})
    finally:
        if conn_local:
            devolver_conexao(conn_local)



def obter_info_execucao(id_maquina, conn_local, cursor_local):
    """
    Obtém informações da Ordem de Produção (OP) em execução para uma máquina específica.
    Recebe conn_local e cursor_local.
    """
    try:
        cursor_local.execute("""
            SELECT TOP 1 
                E.IDExecucao, 
                O.CodigoOrdem, 
                P.NomeProduto, 
                E.QuantidadeProduzida, 
                P.TempoCicloSegundos,
                P.FatorMultiplicacao,
                P.UnidadesPorCaixa,
                E.DataHoraInicio
            FROM TBL_ExecucaoOP E
            JOIN TBL_OrdemProducao O ON E.IDOrdem = O.IDOrdem
            JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
            WHERE E.IDMaquina = ? AND E.Status = 'Em Execucao'
            ORDER BY E.DataHoraInicio DESC
        """, id_maquina)
        
        execucao = cursor_local.fetchone()
        
        if execucao:
            tempo_execucao_segundos = (datetime.now() - execucao.DataHoraInicio).total_seconds()
            
            tempo_ciclo = float(execucao.TempoCicloSegundos) if execucao.TempoCicloSegundos else 0.0
            fator_multiplicacao = float(execucao.FatorMultiplicacao) if execucao.FatorMultiplicacao else 1.0
            quantidade_produzida = float(execucao.QuantidadeProduzida) if execucao.QuantidadeProduzida else 0.0
            
            if tempo_ciclo > 0:
                vel_planejada = (60.0 / tempo_ciclo) * fator_multiplicacao
            else:
                vel_planejada = 0.0

            if tempo_execucao_segundos > 0:
                vel_real = (quantidade_produzida / tempo_execucao_segundos) * 60.0
            else:
                vel_real = 0.0
            
            performance_pct = 0.0
            if vel_planejada > 0:
                performance_pct = (vel_real / vel_planejada) * 100.0
            
            return {
                'id_execucao': execucao.IDExecucao,
                'ordem': execucao.CodigoOrdem,
                'produto': execucao.NomeProduto,
                'produzido': execucao.QuantidadeProduzida,
                'tempo_ciclo': tempo_ciclo,
                'fator_multiplicacao': fator_multiplicacao,
                'unidades_por_caixa': float(execucao.UnidadesPorCaixa) if execucao.UnidadesPorCaixa else 0.0,
                'data_hora_inicio': execucao.DataHoraInicio,
                'tempo_execucao_segundos': round(tempo_execucao_segundos, 2),
                'vel_planejada': round(vel_planejada, 2),
                'vel_real': round(vel_real, 2),
                'performance_pct': round(performance_pct, 2)
            }
        else:
            return None
            
    except Exception as e:
        logger.error(f"Erro ao obter informações de execução da OP para máquina {id_maquina}: {str(e)}", exc_info=True)
        return None

def calcular_disponibilidade(id_maquina, conn_local, cursor_local):
    """
    Calcula a disponibilidade de uma máquina com base nos registros de status.
    Recebe conn_local e cursor_local.
    """
    try:
        # Usamos a view vw_Disponibilidade_Dia que já faz a maior parte do trabalho.
        # Certifique-se que esta view está criada e funcional no seu banco.
        cursor_local.execute("""
            SELECT DisponibilidadePercentual
            FROM vw_Disponibilidade_Dia
            WHERE IDMaquina = ?
            AND CONVERT(DATE, DataHoraInicio) = CONVERT(DATE, GETDATE())
        """, id_maquina)
        
        resultado = cursor_local.fetchone()
        
        if resultado and resultado.DisponibilidadePercentual is not None:
            disponibilidade_pct = float(resultado.DisponibilidadePercentual)
        else:
            # Fallback manual se a view não retornar dados para o dia atual
            data_atual = datetime.now().date()
            data_inicio = datetime.combine(data_atual, datetime.min.time())
            data_fim = datetime.combine(data_atual, datetime.max.time())
            
            cursor_local.execute("""
                SELECT COALESCE(SUM(
                    DATEDIFF(second, DataHoraInicio, 
                        CASE 
                            WHEN DataHoraFim IS NULL THEN GETDATE() 
                            ELSE DataHoraFim 
                        END
                    )
                ), 0) AS TempoExecucaoSegundos
                FROM TBL_StatusMaquina
                WHERE IDMaquina = ? 
                AND DataHoraInicio >= ? 
                AND (DataHoraFim IS NULL OR DataHoraFim <= ?)
                AND Status = 1
            """, id_maquina, data_inicio, data_fim)
            
            resultado_execucao = cursor_local.fetchone()
            tempo_execucao_segundos = float(resultado_execucao.TempoExecucaoSegundos) if resultado_execucao else 0.0
            
            cursor_local.execute("""
                SELECT COALESCE(SUM(
                    DATEDIFF(second, DataHoraInicio, 
                        CASE 
                            WHEN DataHoraFim IS NULL THEN GETDATE() 
                            ELSE DataHoraFim 
                        END
                    )
                ), 0) AS TempoTotalSegundos
                FROM TBL_StatusMaquina
                WHERE IDMaquina = ? 
                AND DataHoraInicio >= ? 
                AND (DataHoraFim IS NULL OR DataHoraFim <= ?)
            """, id_maquina, data_inicio, data_fim)
            
            resultado_total = cursor_local.fetchone()
            tempo_total_segundos = float(resultado_total.TempoTotalSegundos) if resultado_total else 0.0
            
            if tempo_total_segundos > 0:
                disponibilidade_pct = (tempo_execucao_segundos / tempo_total_segundos) * 100.0
            else:
                disponibilidade_pct = 0.0
        
        return {
            'Disponibilidade_Pct': round(disponibilidade_pct, 2),
            'IDMaquina': id_maquina
        }
        
    except Exception as e:
        logger.error(f"Erro ao calcular disponibilidade para máquina {id_maquina}: {str(e)}", exc_info=True)
        return {
            'Disponibilidade_Pct': 0.0,
            'IDMaquina': id_maquina
        }        

@app.route('/')
def index():
    return redirect(url_for('cadastro_produto'))

@app.route('/adicionar_op/<int:id_maquina>', methods=['GET'])
@login_requerido
def adicionar_op(id_maquina):
    """
    Renderiza a página para adicionar uma OP a uma máquina específica.
    VERSÃO MELHORADA: Inclui Qtd Planejada, Data e Tempo Previsto.
    """
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("SELECT NomeMaquina FROM TBL_Recurso WHERE IDMaquina = ?", (id_maquina,))
        maquina = cursor_local.fetchone()
        if not maquina:
            flash(f"Máquina com ID {id_maquina} não encontrada.", "error")
            return redirect(url_for('dashboard'))
        
        nome_maquina = maquina.NomeMaquina

        # --- QUERY ATUALIZADA COM DADOS PARA CÁLCULO DE TEMPO ---
        cursor_local.execute("""
            SELECT
                O.IDOrdem, O.CodigoOrdem, P.NomeProduto,
                OPO.IDOrdemOperacao,
                OPO.NumeroOperacao,
                OPO.Descricao AS DescricaoOperacao,
                
                -- Quantidade Produzida (Real)
                ISNULL((SELECT SUM(Quantidade) FROM VW_EventoProducaoComCicloReal 
                        WHERE IDOrdemProducao = O.IDOrdem AND TipoValor IN ('BOA', 'ESTORNO')), 0) AS QuantidadeProduzida,
                
                -- Quantidade Planejada (Prioriza Operação, senão Ordem)
                ISNULL(OPO.QuantidadePlanejada, O.QuantidadePlanejada) AS QuantidadePlanejada,
                
                -- Dados para cálculo de tempo
                P.TempoCicloSegundos,
                ISNULL(O.FatorMultiplicacaoOrdem, P.FatorMultiplicacao) as FatorMultiplicacao,
                OPO.TempoSetupPlanejadoMinutos,
                
                -- Data
                O.DataInicioPlanejada,

                -- Dados de Fila (se já estiver em alguma)
                F.IDMaquina AS IDMaquinaFila,
                R.NomeMaquina AS NomeRecursoFila
            FROM TBL_OrdemProducao_Operacoes OPO
            JOIN TBL_OrdemProducao O ON OPO.IDOrdem = O.IDOrdem
            JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
            LEFT JOIN TBL_FilaOrdem F ON OPO.IDOrdemOperacao = F.IDOrdemOperacao
            LEFT JOIN TBL_Recurso R ON F.IDMaquina = R.IDMaquina
            WHERE
                O.IDStatus IN (2, 3, 5) 
                AND OPO.StatusOperacao = 'Pendente'
                AND OPO.IDOrdemOperacao NOT IN (
                    SELECT IDOrdemOperacao FROM TBL_ExecucaoOP WHERE Status IN ('Em Execucao', 'Em Setup') AND IDOrdemOperacao IS NOT NULL
                )
            ORDER BY O.CodigoOrdem, OPO.Sequencia
        """)
        
        # Processar resultados para calcular o tempo previsto
        ordens_raw = cursor_local.fetchall()
        ordens_disponiveis = []

        for row in ordens_raw:
            # Converte row para dict para podermos adicionar campos calculados
            ordem = dict(zip([column[0] for column in cursor_local.description], row))
            
            # Cálculo do Tempo Previsto
            qtd_plan = float(ordem['QuantidadePlanejada'] or 0)
            qtd_prod = float(ordem['QuantidadeProduzida'] or 0)
            qtd_pendente = max(0, qtd_plan - qtd_prod)
            
            ciclo_seg = float(ordem['TempoCicloSegundos'] or 0)
            fator = float(ordem['FatorMultiplicacao'] or 1)
            setup_min = float(ordem['TempoSetupPlanejadoMinutos'] or 0)
            
            tempo_previsto_min = 0
            if ciclo_seg > 0 and fator > 0:
                # (Qtd * Ciclo / Fator) / 60 para virar minutos + Setup
                tempo_producao_min = (qtd_pendente * ciclo_seg / fator) / 60
                tempo_previsto_min = tempo_producao_min + setup_min
            
            ordem['TempoPrevisto'] = round(tempo_previsto_min, 0) # Arredonda para minutos inteiros
            ordens_disponiveis.append(ordem)

        return render_template('adicionar_op.html',
                               id_maquina=id_maquina,
                               nome_maquina=nome_maquina,
                               ordens_disponiveis=ordens_disponiveis)

    except Exception as e:
        logger.error(f"Erro ao carregar a página para adicionar OP: {e}", exc_info=True)
        flash("Ocorreu um erro ao carregar a página.", "error")
        return redirect(url_for('dashboard'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
def _processar_interrupcao_em_background(id_execucao, id_ordem, id_produto, id_maquina, id_ordem_operacao):
    """
    Função executada em background para processar o consumo de estoque
    e reordenar a fila após uma interrupção, sem travar a requisição web.
    """
    conn_thread = None
    try:
        # 1. Obter uma nova conexão para este thread
        conn_thread = obter_conexao() 
        cursor_thread = conn_thread.cursor()
        
        logger.info(f"[BG THREAD] Iniciando consumo de estoque para interrupção da Execução ID {id_execucao}...")
        
        # 2. Executar a função lenta de consumo de estoque
        _consumir_estoque_para_ordem(cursor_thread, id_ordem, id_execucao)
        
        logger.info(f"[BG THREAD] Consumo de estoque concluído. Reordenando fila da máquina {id_maquina}...")
        
        # 3. Executar a reordenação da fila
        reordenar_fila(conn_thread, cursor_thread, id_maquina)
        
        # 4. Commit final
        conn_thread.commit()
        logger.info(f"[BG THREAD] Processo de interrupção (consumo e fila) para Execução ID {id_execucao} finalizado com sucesso.")
        
    except EstoqueInsuficienteError as e_estoque:
        if conn_thread: conn_thread.rollback()
        # Loga o erro. O usuário já foi notificado, mas o estoque não foi consumido.
        logger.error(f"[BG THREAD] ERRO DE ESTOQUE durante processamento de interrupção: {e_estoque}", exc_info=True)
        # NOTA: A OP já foi para a fila. A lógica de _verificar_estoque_para_op deve pegar isso na próxima vez.
        
    except Exception as e:
        if conn_thread: conn_thread.rollback()
        logger.error(f"[BG THREAD] Erro CRÍTICO ao processar interrupção em background: {e}", exc_info=True)
    finally:
        if conn_thread:
            devolver_conexao(conn_thread) # Devolve a conexão ao pool
            
@app.route('/interromper_op', methods=['POST'])
@login_requerido
def interromper_op():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        data = request.get_json()
        id_maquina = data.get('id_maquina')

        if not id_maquina:
            return jsonify({'success': False, 'message': 'ID da máquina não fornecido.'}), 400

        # --- Busca informações essenciais (RÁPIDO) ---
        cursor_local.execute("""
            SELECT TOP 1 E.IDExecucao, E.IDOrdem, O.IDProduto, E.IDOrdemOperacao
            FROM TBL_ExecucaoOP E
            JOIN TBL_OrdemProducao O ON E.IDOrdem = O.IDOrdem
            WHERE E.IDMaquina = ? AND E.Status IN ('Em Execucao', 'Em Setup')
            ORDER BY E.DataHoraInicio DESC
        """, (id_maquina,))
        execucao_ativa = cursor_local.fetchone()

        if not execucao_ativa:
            return jsonify({'success': False, 'message': 'Nenhuma ordem em execução encontrada.'}), 404

        # --- AÇÕES RÁPIDAS (EXECUTADAS IMEDIATAMENTE) ---
        
        # 1. Atualiza status da Execução e da Ordem
        cursor_local.execute("UPDATE TBL_ExecucaoOP SET DataHoraFim = GETDATE(), Status = 'Interrompido' WHERE IDExecucao = ?", (execucao_ativa.IDExecucao,))
        cursor_local.execute("UPDATE TBL_OrdemProducao SET IDStatus = 3 WHERE IDOrdem = ?", (execucao_ativa.IDOrdem,))
        
        if execucao_ativa.IDOrdemOperacao:
            # 2. Reseta o status da OPERAÇÃO para 'Pendente'
            cursor_local.execute("UPDATE TBL_OrdemProducao_Operacoes SET StatusOperacao = 'Pendente' WHERE IDOrdemOperacao = ?", (execucao_ativa.IDOrdemOperacao,))
        
            # 3. Coloca a OPERAÇÃO específica de volta na fila
            try:
                cursor_local.execute(
                    "INSERT INTO TBL_FilaOrdem (IDMaquina, IDOrdem, StatusFila, OrdemFila, IDOrdemOperacao) VALUES (?, ?, 'pendente', 0, ?)", 
                    (id_maquina, execucao_ativa.IDOrdem, execucao_ativa.IDOrdemOperacao)
                )
            except pyodbc.IntegrityError:
                logger.warning(f"Operação {execucao_ativa.IDOrdemOperacao} já na fila da máquina {id_maquina}. Inserção ignorada.")
                pass
        
        # 4. Commit das ações rápidas
        conn_local.commit()
        
        # --- AÇÕES LENTAS (EXECUTADAS EM BACKGROUND) ---
        
        # 5. Dispara a thread para consumo de estoque e reordenação da fila
        #    (Removemos a chamada direta a _consumir_estoque_para_ordem e reordenar_fila daqui)
        threading.Thread(target=_processar_interrupcao_em_background, args=(
            execucao_ativa.IDExecucao,
            execucao_ativa.IDOrdem,
            execucao_ativa.IDProduto,
            id_maquina,
            execucao_ativa.IDOrdemOperacao
        )).start()
        
        logger.info(f"Requisição de interrupção para maq {id_maquina} respondida. Thread de consumo iniciada.")
        
        # 6. Responde ao usuário IMEDIATAMENTE
        return jsonify({'success': True, 'message': 'Interrupção registrada! O consumo de estoque está sendo processado.'})

    except EstoqueInsuficienteError as e: # Este erro não deve mais acontecer aqui, mas mantemos
        if conn_local: conn_local.rollback()
        logger.warning(f"Operação de interrupção bloqueada por falta de estoque: {e}")
        return jsonify({'success': False, 'message': str(e)}), 400
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro CRÍTICO ao interromper OP: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Ocorreu um erro inesperado no servidor.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)


# ROTA FINALIZAR OPERAÇÃO (VERSÃO CORRIGIDA - CALCULA SOMA TOTAL AO FINALIZAR)
@app.route('/finalizar_operacao', methods=['POST'])
@login_requerido
def finalizar_operacao():
    conn_local = None
    data = request.json
    id_maquina = data.get('id_maquina')
    # Variáveis para log e controle
    id_ordem = None
    id_ordem_operacao = None # Operação sendo finalizada
    id_execucao = None
    id_produto = None
    # Definindo localmente apenas para garantir (melhor globalmente)
    ID_STATUS_FINALIZADA = 4 # Verifique este ID no seu banco de dados TBL_StatusOrdemProducao

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # --- Bloco para encontrar a execução e operação sendo finalizada ---
        cursor_local.execute("""
            SELECT TOP 1 EX.IDExecucao, OP.IDOrdem, OP.IDProduto, EX.IDOrdemOperacao
            FROM TBL_ExecucaoOP EX
            JOIN TBL_OrdemProducao OP ON EX.IDOrdem = OP.IDOrdem
            WHERE EX.IDMaquina = ? AND EX.Status IN ('Em Execucao', 'Em Setup')
            ORDER BY EX.DataHoraInicio DESC
        """, (id_maquina,))
        operacao_em_execucao = cursor_local.fetchone()

        if operacao_em_execucao:
             id_execucao = operacao_em_execucao.IDExecucao
             id_ordem = operacao_em_execucao.IDOrdem
             id_produto = operacao_em_execucao.IDProduto
             id_ordem_operacao = operacao_em_execucao.IDOrdemOperacao 
             if not id_ordem_operacao:
                 logger.warning(f"Execução ativa {id_execucao} na máquina {id_maquina} não tem IDOrdemOperacao vinculado.")
                 cursor_local.execute("""
                    SELECT TOP 1 IDOrdemOperacao FROM TBL_OrdemProducao_Operacoes
                    WHERE IDOrdem = ? AND StatusOperacao IN ('Em Execucao', 'Em Setup', 'Pendente')
                    ORDER BY Sequencia ASC """, (id_ordem,))
                 op_candidata = cursor_local.fetchone()
                 if op_candidata:
                     id_ordem_operacao = op_candidata.IDOrdemOperacao
                     logger.info(f"Assumindo finalização da operação {id_ordem_operacao} (primeira não finalizada encontrada).")
                 else:
                     logger.error(f"Não foi possível determinar a operação específica sendo finalizada para a ordem {id_ordem} na máquina {id_maquina}.")
        else:
             logger.error(f"Nenhuma execução ativa encontrada para a máquina {id_maquina} ao tentar finalizar operação.")
             return jsonify({'success': False, 'message': 'Nenhuma execução ativa encontrada para esta máquina.'}), 400
        # --- Fim do bloco ---

        logger.info(f"Iniciando finalização (Lógica CORRIGIDA COM SOMA): Maquina={id_maquina}, Ordem={id_ordem}, Execucao={id_execucao}, Operacao={id_ordem_operacao or 'N/VINC'}")

        # Consome estoque de MP
        _consumir_estoque_para_ordem(cursor_local, id_ordem, id_execucao)

        # ==============================================================================
        # CORREÇÃO PRINCIPAL AQUI: Atualiza QuantidadeProduzida somando os eventos
        # ==============================================================================
        cursor_local.execute("""
            UPDATE TBL_ExecucaoOP 
            SET Status = 'Finalizada', 
                DataHoraFim = GETDATE(),
                QuantidadeProduzida = (
                    SELECT ISNULL(SUM(Quantidade), 0)
                    FROM VW_EventoProducaoComCicloReal
                    WHERE IDExecucao = ? AND TipoValor IN ('BOA', 'ESTORNO')
                )
            WHERE IDExecucao = ?
        """, (id_execucao, id_execucao))
        # ==============================================================================

        # Finaliza a operação específica (SE tivermos o ID dela)
        if id_ordem_operacao:
            cursor_local.execute("UPDATE TBL_OrdemProducao_Operacoes SET StatusOperacao = 'Finalizada' WHERE IDOrdemOperacao = ?", (id_ordem_operacao,))
        else:
            logger.warning("Não foi possível atualizar o status da operação específica por falta de ID.")

        # --- LÓGICA DE VERIFICAÇÃO DE CONCLUSÃO DA ORDEM (CORRIGIDA) ---
        cursor_local.execute("SELECT COUNT(*) as Pendentes FROM TBL_OrdemProducao_Operacoes WHERE IDOrdem = ? AND StatusOperacao <> 'Finalizada'", (id_ordem,))
        operacoes_pendentes = cursor_local.fetchone().Pendentes

        flash_message = f"Operação ID {id_ordem_operacao or '?'} finalizada com sucesso!"

        # Se não há mais NENHUMA operação pendente na ordem...
        if operacoes_pendentes == 0:
            logger.info(f"Todas as operações da Ordem {id_ordem} estão finalizadas. Esta foi a última operação a ser concluída. Processando finalização da Ordem e estoque de PA.")
            
            # ... Busca a ÚLTIMA operação do roteiro (pela Sequencia)
            cursor_local.execute("SELECT TOP 1 IDOrdemOperacao FROM TBL_OrdemProducao_Operacoes WHERE IDOrdem = ? ORDER BY Sequencia DESC", (id_ordem,))
            ultima_op_row = cursor_local.fetchone()
            
            if not ultima_op_row:
                 logger.error(f"[Estoque PA] Não foi possível encontrar a última operação do roteiro para a Ordem {id_ordem}. O estoque de PA não será atualizado.")
                 cursor_local.execute("UPDATE TBL_OrdemProducao SET IDStatus = ? WHERE IDOrdem = ?", (ID_STATUS_FINALIZADA, id_ordem,))
                 flash_message = "Última operação concluída! Ordem Finalizada. (AVISO: Roteiro inválido, estoque de PA não atualizado)."
            else:
                id_ultima_operacao_da_ordem = ultima_op_row.IDOrdemOperacao
                logger.info(f"[Estoque PA] A última operação do roteiro é a {id_ultima_operacao_da_ordem}. Calculando a produção líquida *apenas* desta operação.")

                # *** CÁLCULO CORRETO DA QUANTIDADE PARA ESTOQUE PA ***
                # Calcula a quantidade líquida produzida SOMENTE nas execuções VINCULADAS à ÚLTIMA OPERAÇÃO
                cursor_local.execute("""
                    SELECT SUM(ev.Quantidade) as TotalLiquidoUltimaOperacao
                    FROM VW_EventoProducaoComCicloReal ev
                    JOIN TBL_ExecucaoOP ex ON ev.IDExecucao = ex.IDExecucao
                    WHERE ex.IDOrdemOperacao = ? AND ev.TipoValor IN ('BOA', 'ESTORNO')
                """, (id_ultima_operacao_da_ordem,)) 
                producao_ultima_op = cursor_local.fetchone()
                quantidade_total_ultima_op = producao_ultima_op.TotalLiquidoUltimaOperacao if producao_ultima_op and producao_ultima_op.TotalLiquidoUltimaOperacao is not None else 0

                logger.info(f"[Estoque PA] Calculado TotalLiquidoUltimaOperacao = {quantidade_total_ultima_op} para Operacao {id_ultima_operacao_da_ordem}. Chamando _adicionar_produto_acabado_ao_estoque...")

                if quantidade_total_ultima_op >= 0:
                    _adicionar_produto_acabado_ao_estoque(cursor_local, id_ordem, id_produto, quantidade_total_ultima_op)
                else:
                    logger.warning(f"[Estoque PA] Ordem {id_ordem}, Última Op {id_ultima_operacao_da_ordem} com produção líquida negativa ({quantidade_total_ultima_op}). Estoque PA não alterado.")

                # Atualiza o status da Ordem para Finalizada
                cursor_local.execute("UPDATE TBL_OrdemProducao SET IDStatus = ? WHERE IDOrdem = ?", (ID_STATUS_FINALIZADA, id_ordem,))
                flash_message = "Última operação concluída! Ordem Finalizada. Estoque de PA atualizado/ajustado para o total produzido nesta etapa."
        
        # --- FIM DA LÓGICA CORRIGIDA ---

        conn_local.commit()
        return jsonify({'success': True, 'message': flash_message})

    # --- Blocos except e finally ---
    except EstoqueInsuficienteError as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro de estoque ao finalizar Operacao={id_ordem_operacao}, Ordem={id_ordem}: {e}")
        return jsonify({'success': False, 'message': str(e)}), 400
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro CRÍTICO ao finalizar Operacao={id_ordem_operacao}, Ordem={id_ordem}: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Erro interno ao finalizar a operação.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/fila_ordens/<int:id_maquina>', methods=['GET', 'POST']) # GET é o principal aqui
@login_requerido
@permissao_requerida('/fila_ordens')
def fila_ordens(id_maquina):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Busca a configuração de unidades por caixa
        usa_unidades_caixa = obter_configuracao('USA_UNIDADES_POR_CAIXA', conn_local, cursor_local) == 'true'
        logger.info(f"Rota fila_ordens: usa_unidades_caixa = {usa_unidades_caixa}")

        # Query SQL Ajustada
        query = """
            SELECT
                f.IDFila, f.OrdemFila, o.IDOrdem, f.IDMaquina, o.CodigoOrdem, p.NomeProduto,
                
                -- >>> ALTERAÇÃO AQUI: Prioriza a Qtd da Operação, se não tiver, usa da Ordem <<<
                ISNULL(opo.QuantidadePlanejada, o.QuantidadePlanejada) AS QuantidadePlanejada,
                
                f.DataInsercao,
                opo.Sequencia, opo.NumeroOperacao, opo.Descricao as DescricaoOperacao, opo.IDOrdemOperacao,
                opo.TempoSetupPlanejadoMinutos,
                p.UnidadesPorCaixa,

                -- Quantidade produzida LÍQUIDA para ESTA OPERAÇÃO específica
                ISNULL((
                    SELECT SUM(ev_op.Quantidade)
                    FROM VW_EventoProducaoComCicloReal ev_op WITH (NOLOCK)
                    JOIN TBL_ExecucaoOP ex_op WITH (NOLOCK) ON ev_op.IDExecucao = ex_op.IDExecucao
                    WHERE ex_op.IDOrdemOperacao = opo.IDOrdemOperacao
                      AND ev_op.TipoValor IN ('BOA', 'ESTORNO')
                ), 0) AS QuantidadeProduzidaOperacao,

                -- Quantidade produzida LÍQUIDA para a ORDEM INTEIRA (usado no tempo previsto)
                -- Nota: Aqui mantemos a soma geral para referência, mas o cálculo abaixo usará a Qtd da Operação
                ISNULL((
                    SELECT SUM(ev_ord.Quantidade)
                    FROM VW_EventoProducaoComCicloReal ev_ord WITH (NOLOCK)
                    WHERE ev_ord.IDOrdemProducao = o.IDOrdem
                      AND ev_ord.TipoValor IN ('BOA', 'ESTORNO')
                ), 0) as QuantidadeProduzidaOrdemTotal,

                -- Tempo de ciclo e fator
                CASE
                    WHEN o.UsarTempoCicloRecurso = 1 AND rp.IDRecursoProduto IS NOT NULL THEN rp.TempoCicloPadraoSegundos
                    ELSE p.TempoCicloSegundos
                END AS TempoCicloFinalSeg,
                o.FatorMultiplicacaoOrdem AS FatorMultiplicacaoFinal

            FROM TBL_FilaOrdem f WITH (NOLOCK)
            JOIN TBL_OrdemProducao_Operacoes opo WITH (NOLOCK) ON f.IDOrdemOperacao = opo.IDOrdemOperacao
            JOIN TBL_OrdemProducao o WITH (NOLOCK) ON opo.IDOrdem = o.IDOrdem
            JOIN TBL_Produto p WITH (NOLOCK) ON p.IDProduto = o.IDProduto
            LEFT JOIN TBL_RecursoProduto rp WITH (NOLOCK) ON o.IDProduto = rp.IDProduto AND opo.IDRecurso = rp.IDRecurso
            WHERE f.IDMaquina = ?
            ORDER BY f.OrdemFila, opo.Sequencia
        """
        cursor_local.execute(query, (id_maquina,))

        operacoes_na_fila = []
        for row in cursor_local.fetchall():
            # Converte a linha do banco para um dicionário
            op_dict = dict(zip([column[0] for column in row.cursor_description], row))

            # --- Cálculo do Tempo Previsto (Atualizado para usar a Qtd da Operação) ---
            tempo_previsto_min = 0.0
            tempo_ciclo_seg = float(op_dict.get('TempoCicloFinalSeg') or 0)
            fator = float(op_dict.get('FatorMultiplicacaoFinal') or 1.0)
            
            # AGORA: Usa a quantidade planejada que veio do SQL (que pode ser a específica da operação)
            qtd_planejada_operacao = float(op_dict.get('QuantidadePlanejada') or 0)
            
            # O que já foi produzido NESTA operação
            qtd_ja_produzida_operacao = float(op_dict.get('QuantidadeProduzidaOperacao') or 0)
            
            # O restante é baseado na meta desta operação específica
            qtd_restante_para_produzir = max(0, qtd_planejada_operacao - qtd_ja_produzida_operacao)
            
            setup_min = float(op_dict.get('TempoSetupPlanejadoMinutos') or 0)

            if tempo_ciclo_seg > 0 and fator > 0 and qtd_restante_para_produzir > 0:
                tempo_producao_seg = (qtd_restante_para_produzir * tempo_ciclo_seg) / fator
                tempo_producao_min = tempo_producao_seg / 60
                tempo_previsto_min = tempo_producao_min + setup_min
            else:
                tempo_previsto_min = setup_min if qtd_restante_para_produzir == 0 else setup_min

            op_dict['TempoPrevistoOperacaoMinutos'] = tempo_previsto_min
            operacoes_na_fila.append(op_dict)

        # Busca nome da máquina e turno atual
        cursor_local.execute("SELECT NomeMaquina FROM TBL_Recurso WHERE IDMaquina = ?", (id_maquina,))
        nome_maquina_row = cursor_local.fetchone()
        nome_maquina = nome_maquina_row.NomeMaquina if nome_maquina_row else f"Máquina ID {id_maquina}"
        id_turno_atual = identificar_turno(conn_local, cursor_local)

        return render_template("fila_ordens.html",
                               operacoes=operacoes_na_fila,
                               id_turno_atual=id_turno_atual,
                               id_maquina=id_maquina,
                               nome_maquina=nome_maquina,
                               usa_unidades_caixa=usa_unidades_caixa
                               )
    except Exception as e:
        logger.error(f"Erro em fila_ordens: {e}", exc_info=True)
        flash("Ocorreu um erro ao carregar a fila de operações.", "error")
        return redirect(url_for('dashboard'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
@app.route('/iniciar_setup_fila', methods=['GET'])
@login_requerido
@permissao_requerida('/iniciar_op_fila')
def iniciar_setup_fila():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_ordem = request.args.get('id_ordem', type=int)
        id_maquina = request.args.get('id_maquina', type=int)
        id_ordem_operacao = request.args.get('id_ordem_operacao', type=int)

        if not all([id_ordem, id_maquina, id_ordem_operacao]):
            flash("Erro: Dados incompletos.", "error")
            return redirect(request.referrer or url_for('dashboard'))

        # Busca ID do Status
        cursor_local.execute("SELECT IDStatus FROM TBL_StatusOrdemProducao WHERE NomeStatus = 'Em Setup'")
        status_setup_row = cursor_local.fetchone()
        ID_STATUS_EM_SETUP = status_setup_row.IDStatus if status_setup_row else 6 

        cursor_local.execute("SELECT IDMotivoParada FROM TBL_MotivoParada WHERE Codigo = '03'")
        motivo_setup_row = cursor_local.fetchone()
        if not motivo_setup_row:
            flash("Erro de Configuração: Motivo de parada 'SETUP' (Código 03) não encontrado.", "error")
            return redirect(request.referrer or url_for('dashboard'))
        id_motivo_setup = motivo_setup_row.IDMotivoParada

        cursor_local.execute("SELECT TOP 1 IDExecucao FROM TBL_ExecucaoOP WHERE IDMaquina = ? AND Status IN ('Em Execucao', 'Em Setup')", (id_maquina,))
        if cursor_local.fetchone():
            flash(f"A máquina já está executando outra OP ou já está em Setup.", "warning")
            return redirect(request.referrer or url_for('dashboard'))

        id_usuario_logado = session.get('usuario_id')
        cursor_local.execute("SELECT IDOperador FROM TBL_Operador WHERE IDUsuario = ? AND Ativo = 1", id_usuario_logado)
        operador_logado = cursor_local.fetchone()
        id_operador = operador_logado.IDOperador if operador_logado else None
        id_turno = identificar_turno(conn_local, cursor_local)

        cursor_local.execute("""
            SELECT ISNULL(SUM(ev.Quantidade), 0) as QuantidadeAnterior
            FROM VW_EventoProducaoComCicloReal ev
            JOIN TBL_ExecucaoOP ex ON ev.IDExecucao = ex.IDExecucao
            WHERE ex.IDOrdemOperacao = ? AND ev.TipoValor IN ('BOA', 'ESTORNO')
        """, (id_ordem_operacao,))
        resultado_soma = cursor_local.fetchone()
        quantidade_anterior = resultado_soma.QuantidadeAnterior if resultado_soma else 0

        cursor_local.execute("DELETE FROM TBL_FilaOrdem WHERE IDOrdemOperacao = ?", (id_ordem_operacao,))
        cursor_local.execute("UPDATE TBL_OrdemProducao SET IDStatus = ? WHERE IDOrdem = ?", (ID_STATUS_EM_SETUP, id_ordem))
        cursor_local.execute("UPDATE TBL_OrdemProducao_Operacoes SET StatusOperacao = 'Em Setup' WHERE IDOrdemOperacao = ?", (id_ordem_operacao,))

        cursor_local.execute("""
            INSERT INTO TBL_ExecucaoOP (IDOrdem, IDMaquina, IDOperador, IDTurno, DataHoraInicio, Status, IDOrdemOperacao, QuantidadeProduzida, IDStatus)
            VALUES (?, ?, ?, ?, GETDATE(), 'Em Setup', ?, ?, ?)
        """, (id_ordem, id_maquina, id_operador, id_turno, id_ordem_operacao, quantidade_anterior, ID_STATUS_EM_SETUP))

        _update_machine_status(conn_local, cursor_local, id_maquina, 0, id_motivo_parada=id_motivo_setup, obs_evento='Início do setup via fila')

        cursor_local.execute("SELECT TempoSetupPlanejadoMinutos FROM TBL_OrdemProducao_Operacoes WHERE IDOrdemOperacao = ?", (id_ordem_operacao,))
        operacao_info = cursor_local.fetchone()
        
        # ===== CORREÇÃO AQUI: Convertendo Decimal para Float =====
        tempo_setup_min = float(operacao_info.TempoSetupPlanejadoMinutos) if operacao_info and operacao_info.TempoSetupPlanejadoMinutos else 0.0
        # =========================================================
        
        if tempo_setup_min > 0:
             cursor_local.execute("""
                SELECT TOP 1 IDRegistroStatus
                FROM TBL_StatusMaquina
                WHERE IDMaquina = ? AND Status = 0 AND IDMotivoParada = ? AND DataHoraFim IS NULL
                ORDER BY DataHoraRegistro DESC
             """, (id_maquina, id_motivo_setup))
             novo_status_setup = cursor_local.fetchone()
             if novo_status_setup:
                 # Agora a multiplicação (float * int) resulta em float, que o timedelta aceita
                 agendar_verificacao_estouro_setup(id_maquina, novo_status_setup.IDRegistroStatus, tempo_setup_min * 60)

        conn_local.commit()
        flash("Setup da operação iniciado com sucesso!", "success")
        return redirect(url_for('dashboard'))

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em iniciar_setup_fila: {e}", exc_info=True)
        flash(f"Ocorreu um erro ao iniciar o setup: {str(e)}", "error")
        return redirect(request.referrer or url_for('dashboard'))
    finally:
        if conn_local: devolver_conexao(conn_local)
            
@app.route('/api/maquina/<int:id_maquina>/historico_ciclos')
@login_requerido
def api_historico_ciclos_maquina(id_maquina):
    conn_local = None
    try:
        limite = request.args.get('limite', default=30, type=int)

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # 1. Obter o ciclo planejado (nenhuma mudança aqui)
        cursor_local.execute("""
            SELECT TOP 1
                CASE
                    WHEN OP.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.TempoCicloPadraoSegundos
                    ELSE P.TempoCicloSegundos
                END AS CicloPlanejadoSeg
            FROM TBL_ExecucaoOP E
            JOIN TBL_OrdemProducao OP ON E.IDOrdem = OP.IDOrdem
            JOIN TBL_Produto P ON OP.IDProduto = P.IDProduto
            LEFT JOIN TBL_RecursoProduto RP ON E.IDMaquina = RP.IDRecurso AND P.IDProduto = RP.IDProduto
            WHERE E.IDMaquina = ? AND E.Status = 'Em Execucao'
        """, (id_maquina,))
        
        ordem_ativa = cursor_local.fetchone()
        ciclo_planejado = float(ordem_ativa.CicloPlanejadoSeg) if ordem_ativa and ordem_ativa.CicloPlanejadoSeg else 0

        # 2. Query modificada para usar MILISSEGUNDOS
        uma_hora_atras = datetime.now() - timedelta(hours=1)
        query_ciclos_reais = f"""
            WITH EventosComLag AS (
                SELECT
                    DataHoraEvento,
                    LAG(DataHoraEvento, 1) OVER (PARTITION BY IDMaquina ORDER BY DataHoraEvento) as HoraEventoAnterior
                FROM VW_EventoProducaoComCicloReal
                WHERE IDMaquina = ? AND TipoValor = 'BOA' AND DataHoraEvento >= ?
            ),
            CiclosRecentes AS (
                SELECT TOP (?)
                    DataHoraEvento,
                    -- **** INÍCIO DA ALTERAÇÃO ****
                    -- Calculamos em milissegundos e dividimos por 1000.0 para forçar o resultado decimal
                    CAST(DATEDIFF(MILLISECOND, HoraEventoAnterior, DataHoraEvento) AS FLOAT) / 1000.0 as CicloRealSegundos
                    -- **** FIM DA ALTERAÇÃO ****
                FROM EventosComLag
                WHERE HoraEventoAnterior IS NOT NULL AND DATEDIFF(SECOND, HoraEventoAnterior, DataHoraEvento) > 0
                ORDER BY DataHoraEvento DESC
            )
            SELECT * FROM CiclosRecentes ORDER BY DataHoraEvento ASC;
        """
        
        cursor_local.execute(query_ciclos_reais, (id_maquina, uma_hora_atras, limite))
        
        historico_ciclos = cursor_local.fetchall()
        
        # 3. Formatar os dados (nenhuma mudança aqui)
        labels = [evento.DataHoraEvento.strftime('%H:%M:%S') for evento in historico_ciclos]
        # O valor aqui já virá com casas decimais do banco
        ciclo_real_data = [evento.CicloRealSegundos for evento in historico_ciclos]
        
        return jsonify({
            'success': True,
            'labels': labels,
            'ciclo_real_data': ciclo_real_data,
            'ciclo_planejado': ciclo_planejado
        })

    except Exception as e:
        logger.error(f"Erro em api_historico_ciclos_maquina: {e}", exc_info=True)
        return jsonify({"success": False, "message": "Erro ao buscar histórico de ciclos"}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)           

@app.route('/api/classificar-parada', methods=['POST'])
@login_requerido
def api_classificar_parada():
    conn_local = None
    try:
        data = request.json
        maquina_id = data.get('maquina_id')
        motivo_id = data.get('motivo_id')
        substituir_parada_checkbox = data.get('substituir_parada', False)
        
        # Captura a observação digitada pelo usuário
        observacao_usuario = data.get('observacao', '') 

        if not maquina_id or not motivo_id:
            return jsonify({"success": False, "message": "Parâmetros incompletos"}), 400

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Verifica status atual da máquina
        cursor_local.execute("""
            SELECT TOP 1 Status, IDRegistroStatus
            FROM TBL_StatusMaquina
            WHERE IDMaquina = ? AND DataHoraFim IS NULL
            ORDER BY DataHoraRegistro DESC
        """, (maquina_id,))
        status_atual_maquina = cursor_local.fetchone()
        current_status_value = status_atual_maquina.Status if status_atual_maquina else -1
        id_registro_status_atual = status_atual_maquina.IDRegistroStatus if status_atual_maquina else None

        # Busca o nome do motivo (apenas para log ou mensagem de retorno, não será mais salvo na Obs)
        nome_do_motivo = "Motivo selecionado"
        try:
            cursor_local.execute("SELECT Descricao FROM TBL_MotivoParada WHERE IDMotivoParada = ?", motivo_id)
            motivo_row = cursor_local.fetchone()
            if motivo_row and motivo_row.Descricao:
                nome_do_motivo = motivo_row.Descricao
        except Exception as e:
            logger.error(f"Erro ao buscar descrição do motivo: {e}")

        # --- LÓGICA ALTERADA AQUI (LIMPEZA DA OBSERVAÇÃO) ---
        # Antes: obs_final = f"{nome_do_motivo} - Obs: {observacao_usuario}"
        # Agora: Salva estritamente o que foi digitado
        
        if observacao_usuario and observacao_usuario.strip():
            # Se o usuário digitou algo, salvamos APENAS o que ele digitou
            obs_final = observacao_usuario.strip()
        else:
            # Se não digitou nada, salvamos NULL (None) para ficar em branco no relatório
            obs_final = None
        # ----------------------------------------------------

        message = ""

        if current_status_value == 1: # MÁQUINA RODANDO -> PARAR
            _update_machine_status(
                conn_local, cursor_local, maquina_id,
                new_status=0, id_motivo_parada=motivo_id, obs_evento=obs_final 
            )
            message = f'Máquina parada e classificada como: {nome_do_motivo}.'

        elif current_status_value == 0: # MÁQUINA JÁ PARADA
            registro_parada_ativo_id = id_registro_status_atual

            if not registro_parada_ativo_id:
                # Caso de segurança se não achar o registro aberto
                _update_machine_status(conn_local, cursor_local, maquina_id, 0, motivo_id, obs_final)
                message = f'Parada classificada: {nome_do_motivo}.'
            
            elif substituir_parada_checkbox:
                # ATUALIZA o motivo da parada existente
                cursor_local.execute("""
                    UPDATE TBL_StatusMaquina SET IDMotivoParada = ?, ObsEvento = ? WHERE IDRegistroStatus = ?
                """, (motivo_id, obs_final, registro_parada_ativo_id))
                
                # Log do evento de atualização
                log_evento = f"Motivo atualizado para: {nome_do_motivo}"
                cursor_local.execute("""
                    INSERT INTO TBL_EventoStatus (IDMaquina, Status, DataHoraEvento, IDMotivoParada, ObsEvento) VALUES (?, 0, GETDATE(), ?, ?)
                """, (maquina_id, motivo_id, log_evento))
                
                message = 'Motivo substituído com sucesso!'
            else:
                # ENCERRA a parada antiga e ABRE uma nova
                now = datetime.now()
                cursor_local.execute("""
                    UPDATE TBL_StatusMaquina SET DataHoraFim = ?, DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, ?) WHERE IDRegistroStatus = ?
                """, (now, now, registro_parada_ativo_id))
                
                _update_machine_status(conn_local, cursor_local, maquina_id, 0, motivo_id, obs_final)
                message = 'Nova parada classificada registrada.'

        else: # SEM STATUS (Primeira vez ou erro)
             _update_machine_status(conn_local, cursor_local, maquina_id, 0, motivo_id, obs_final)
             message = f'Parada classificada: {nome_do_motivo}.'

        conn_local.commit()

        # Disparo de alarme (se configurado no motivo)
        try:
            cursor_local.execute("SELECT IDMotivoAlarmeGatilho FROM TBL_MotivoParada WHERE IDMotivoParada = ?", (motivo_id,))
            resultado_gatilho = cursor_local.fetchone()
            if resultado_gatilho and resultado_gatilho.IDMotivoAlarmeGatilho:
                obs_alarme = f"Gatilho automático: {nome_do_motivo}"
                if obs_final:
                    obs_alarme += f" ({obs_final})"
                
                disparar_alarme(id_motivo_alarme=resultado_gatilho.IDMotivoAlarmeGatilho, tipo_disparo='Automático', id_maquina=maquina_id, id_motivo_parada_gatilho=motivo_id, id_usuario_contexto=session.get('usuario_id'), observacao=obs_alarme)
        except Exception as e_gatilho:
            logger.error(f"Erro gatilho alarme: {e_gatilho}")

        return jsonify({'success': True, 'message': message})

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro CRÍTICO ao classificar parada: {str(e)}", exc_info=True)
        return jsonify({"success": False, "message": "Erro interno."}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
# Rota para obter os motivos de parada
@app.route('/api/motivos-parada', methods=['GET'])
def api_motivos_parada():
    try:
        conn = conectar_bd()
        cursor = conn.cursor()
        
        # Consulta todos os motivos de parada
        cursor.execute("""
            SELECT IDMotivoParada, Descricao, FlgPlanejada, Codigo, Ativo
            FROM TBL_MotivoParada
            ORDER BY Codigo
        """)
        
        motivos = []
        for row in cursor.fetchall():
            # Converter explicitamente para booleanos
            motivos.append({
                'IDMotivoParada': row.IDMotivoParada,
                'Descricao': row.Descricao,
                'FlgPlanejada': bool(row.FlgPlanejada),
                'Codigo': row.Codigo,
                'Ativo': bool(row.Ativo)
            })
        
        return jsonify(motivos)
    
    except Exception as e:
        logger.error(f"Erro ao obter motivos de parada: {str(e)}", exc_info=True)
        return jsonify([])
    finally:
        if conn:
            conn.close()
            
@app.route('/api/iniciar-producao', methods=['POST'])
@login_requerido
def api_iniciar_producao():
    conn_local = None
    try:
        data = request.json
        maquina_id = data.get('maquina_id')

        if not maquina_id:
            return jsonify({'success': False, 'message': 'ID da máquina é obrigatório.'}), 400

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # CORREÇÃO DEFINITIVA:
        # Removemos a lógica antiga que mexia direto na tabela TBL_StatusMaquina
        # e passamos a chamar a nossa função central, que já contém toda a inteligência.
        _update_machine_status(
            conn_local, 
            cursor_local, 
            maquina_id, 
            new_status=1, 
            obs_evento='Produção iniciada manualmente via dashboard'
        )

        conn_local.commit()
        return jsonify({'success': True, 'message': 'Máquina iniciada em produção com sucesso!'})

    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro ao iniciar produção via API: {e}", exc_info=True)
        return jsonify({'success': False, 'message': f'Erro ao iniciar produção: {str(e)}'}), 500

    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/relacionamento_alarme_grupo', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relacionamento_alarme_grupo') # Lembre-se de cadastrar esta permissão no sistema
def relacionamento_alarme_grupo():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            id_alarme = request.form.get('id_alarme')
            grupos_selecionados_ids = request.form.getlist('grupos_notificados')

            if not id_alarme:
                flash("É necessário selecionar um motivo de alarme.", "error")
                return redirect(url_for('relacionamento_alarme_grupo'))

            # 1. Deleta os relacionamentos antigos para este alarme
            cursor_local.execute("DELETE FROM TBL_AlarmeGrupoUsuario WHERE IDMotivoAlarme = ?", (id_alarme,))

            # 2. Insere os novos relacionamentos
            if grupos_selecionados_ids:
                for id_grupo in grupos_selecionados_ids:
                    cursor_local.execute("INSERT INTO TBL_AlarmeGrupoUsuario (IDMotivoAlarme, IDGrupo) VALUES (?, ?)", (id_alarme, id_grupo))
            
            conn_local.commit()
            flash("Relacionamento salvo com sucesso!", "success")
            return redirect(url_for('relacionamento_alarme_grupo', id_alarme_selecionado=id_alarme))

        # Lógica GET
        cursor_local.execute("SELECT IDMotivoAlarme, Nome, TipoAlarme FROM TBL_MotivoAlarme WHERE Ativo = 1 ORDER BY Nome")
        alarmes = cursor_local.fetchall()
        
        id_alarme_selecionado = request.args.get('id_alarme_selecionado')

        return render_template('relacionamento_alarme_grupo.html', 
                               alarmes=alarmes,
                               id_alarme_selecionado=id_alarme_selecionado)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em /relacionamento_alarme_grupo: {e}", exc_info=True)
        flash("Ocorreu um erro ao carregar a página de relacionamentos.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/api/alarme/<int:id_alarme>/grupos')
@login_requerido
def api_alarme_grupos(id_alarme):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Grupos já associados
        cursor_local.execute("""
            SELECT G.IDGrupo, G.NomeGrupo
            FROM TBL_AlarmeGrupoUsuario AG
            JOIN TBL_GrupoUsuario G ON AG.IDGrupo = G.IDGrupo
            WHERE AG.IDMotivoAlarme = ? AND G.Ativo = 1
            ORDER BY G.NomeGrupo
        """, (id_alarme,))
        grupos_notificados = [dict(zip([column[0] for column in cursor_local.description], row)) for row in cursor_local.fetchall()]

        # Grupos ainda não associados
        cursor_local.execute("""
            SELECT IDGrupo, NomeGrupo
            FROM TBL_GrupoUsuario
            WHERE Ativo = 1 AND IDGrupo NOT IN (SELECT IDGrupo FROM TBL_AlarmeGrupoUsuario WHERE IDMotivoAlarme = ?)
            ORDER BY NomeGrupo
        """, (id_alarme,))
        grupos_disponiveis = [dict(zip([column[0] for column in cursor_local.description], row)) for row in cursor_local.fetchall()]

        return jsonify({
            'notificados': grupos_notificados,
            'disponiveis': grupos_disponiveis
        })

    except Exception as e:
        logger.error(f"Erro na API de grupos de alarme: {e}", exc_info=True)
        return jsonify({'error': 'Erro interno do servidor'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local) 

@app.route('/remover_fila/<int:id_maquina>/<int:id_ordem>', methods=['POST'])
@login_requerido
@permissao_requerida('/remover_fila') # Assegurar que esta rota tem permissão
def remover_fila(id_maquina, id_ordem):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("DELETE FROM TBL_FilaOrdem WHERE IDMaquina = ? AND IDOrdem = ?", (id_maquina, id_ordem))
        conn_local.commit()
        flash("Ordem removida da fila com sucesso!", "success")
        return redirect(url_for('fila_ordens', id_maquina=id_maquina))
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em remover_fila: {e}", exc_info=True)
        flash("Ocorreu um erro ao remover a ordem da fila.", "error")
        return redirect(url_for('fila_ordens', id_maquina=id_maquina))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
# Em planner_app.py, substitua a rota /relatorio_producao inteira por esta VERSÃO ROBUSTA FINAL:

@app.route('/relatorio_producao', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relatorio_producao')
def relatorio_producao():
    conn_local = None
    resultados = []
    dados_grafico_tendencia = {}
    kpis = {
        'total_produzido': 0, 'total_refugado': 0, 'taxa_refugo_geral': 0,
        'eficiencia_geral': 0, 'total_caixas': 0
    }

    filtros = {
        "data_inicio": request.form.get("data_inicio", (datetime.now() - timedelta(days=7)).strftime('%Y-%m-%d')),
        "data_fim": request.form.get("data_fim", datetime.now().strftime('%Y-%m-%d')),
        "id_maquina": request.form.get("id_maquina"),
        "id_produto": request.form.get("id_produto"),
        "id_operador": request.form.get("id_operador"),
        "codigo_ordem": request.form.get("codigo_ordem", "")
    }

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        usa_unidades_caixa = obter_configuracao('USA_UNIDADES_POR_CAIXA', conn_local, cursor_local) == 'true'

        maquinas = cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina").fetchall()
        produtos = cursor_local.execute("SELECT IDProduto, CodigoProduto, NomeProduto FROM TBL_Produto WHERE Habilitado = 1 ORDER BY NomeProduto").fetchall()
        operadores_lista = cursor_local.execute("SELECT IDOperador, NomeOperador FROM TBL_Operador WHERE Ativo = 1 ORDER BY NomeOperador").fetchall()

        if request.method == 'POST':
            query = '''
                SET DATEFORMAT ymd;
                WITH EventosComDataTurno AS (
                    SELECT
                        E.*, T.NomeTurno, T.IniciaDiaAnterior, T.HoraInicio AS HoraInicioTurno,
                        CASE
                            WHEN T.IniciaDiaAnterior = 1 AND CAST(E.DataHoraEvento AS TIME) < CAST(T.HoraInicio AS TIME)
                            THEN CAST(DATEADD(day, -1, E.DataHoraEvento) AS DATE)
                            ELSE CAST(E.DataHoraEvento AS DATE)
                        END AS DataReferenciaTurno
                    FROM VW_EventoProducaoComCicloReal E
                    LEFT JOIN TBL_Turno T ON E.IDTurno = T.IDTurno
                )
                SELECT
                    EVT.DataReferenciaTurno, MIN(EVT.DataHoraEvento) AS PrimeiroEvento,
                    
                    ISNULL(R.NomeMaquina, 'Máquina Desconhecida') AS NomeMaquina,
                    ISNULL(O.CodigoOrdem, 'Sem Ordem') AS CodigoOrdem,
                    ISNULL(P.CodigoProduto, '-') AS CodigoProduto,
                    ISNULL(P.NomeProduto, 'Sem Produto') AS NomeProduto,
                    ISNULL(OPO.NumeroOperacao, '-') AS NumeroOperacao, 
                    ISNULL(OPO.Descricao, 'Operação não vinculada') AS DescricaoOperacao,

                    ISNULL(EVT.NomeTurno, 'Fora de Turno') AS NomeTurno,
                    EVT.IDTurno,

                    -- >>> ALTERAÇÃO AQUI: Prioriza a quantidade da Operação <<<
                    ISNULL(OPO.QuantidadePlanejada, O.QuantidadePlanejada) AS QuantidadePlanejada,
                    
                    P.UnidadesPorCaixa,
                    ISNULL(SUM(CASE WHEN EVT.TipoValor = 'BOA' THEN EVT.Quantidade ELSE 0 END), 0) AS QuantidadeProduzidaBruta,
                    ISNULL(SUM(CASE WHEN EVT.TipoValor IN ('BOA', 'ESTORNO') THEN EVT.Quantidade ELSE 0 END), 0) AS QuantidadeProduzidaLiquida,
                    ISNULL(SUM(CASE WHEN EVT.TipoValor = 'REFUGO' THEN EVT.Quantidade ELSE 0 END), 0) AS QuantidadeRefugada,
                    MAX(Op.NomeOperador) AS NomeOperador,
                    DATEDIFF(SECOND, MIN(EVT.DataHoraEvento), MAX(EVT.DataHoraEvento)) AS DuracaoSegundosGrupo
                FROM EventosComDataTurno EVT
                
                LEFT JOIN TBL_ExecucaoOP EX ON EVT.IDExecucao = EX.IDExecucao
                LEFT JOIN TBL_OrdemProducao_Operacoes OPO ON EX.IDOrdemOperacao = OPO.IDOrdemOperacao
                LEFT JOIN TBL_Recurso R ON EVT.IDMaquina = R.IDMaquina
                LEFT JOIN TBL_OrdemProducao O ON EVT.IDOrdemProducao = O.IDOrdem
                LEFT JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
                LEFT JOIN TBL_Operador Op ON EVT.IDOperador = Op.IDOperador
                WHERE 1=1 AND EVT.TipoValor IN ('BOA', 'REFUGO', 'ESTORNO')
            '''
            params = []

            if filtros["data_inicio"]:
                query += " AND EVT.DataReferenciaTurno >= ?"
                params.append(filtros["data_inicio"])
            if filtros["data_fim"]:
                query += " AND EVT.DataReferenciaTurno <= ?"
                params.append(filtros["data_fim"])
            if filtros["id_maquina"]:
                query += " AND EVT.IDMaquina = ?"
                params.append(int(filtros["id_maquina"]))
            if filtros["id_produto"]:
                query += " AND P.IDProduto = ?" 
                params.append(int(filtros["id_produto"]))
            if filtros["id_operador"]:
                query += " AND EVT.IDOperador = ?"
                params.append(int(filtros["id_operador"]))
            if filtros["codigo_ordem"]:
                query += " AND O.CodigoOrdem LIKE ?" 
                params.append(f"%{filtros['codigo_ordem']}%")

            query += '''
                GROUP BY
                    EVT.DataReferenciaTurno,
                    ISNULL(EVT.NomeTurno, 'Fora de Turno'),
                    EVT.IDTurno,
                    ISNULL(R.NomeMaquina, 'Máquina Desconhecida'),
                    ISNULL(O.CodigoOrdem, 'Sem Ordem'),
                    ISNULL(P.CodigoProduto, '-'),
                    ISNULL(P.NomeProduto, 'Sem Produto'),
                    ISNULL(OPO.NumeroOperacao, '-'), 
                    ISNULL(OPO.Descricao, 'Operação não vinculada'),
                    
                    -- >>> ALTERAÇÃO AQUI: Agrupa por ambas as colunas para o ISNULL funcionar <<<
                    O.QuantidadePlanejada, 
                    OPO.QuantidadePlanejada,
                    
                    P.UnidadesPorCaixa
                ORDER BY
                    EVT.DataReferenciaTurno DESC, NomeMaquina, EVT.IDTurno
            '''

            logger.debug(f"Executando query relatorio_producao: {query} com params: {params}")
            cursor_local.execute(query, params)
            resultados_raw = cursor_local.fetchall()
            logger.info(f"Query relatorio_producao retornou {len(resultados_raw)} linhas.")

            resultados = []
            for row in resultados_raw:
                 row_dict = dict(zip([column[0] for column in row.cursor_description], row))
                 row_dict['DataHoraInicio'] = row_dict.pop('DataReferenciaTurno', None)
                 if not row_dict.get('DataHoraInicio'):
                     row_dict['DataHoraInicio'] = row_dict.pop('PrimeiroEvento', None)
                 resultados.append(row_dict)

            if resultados:
                total_produzido = sum(float(r.get('QuantidadeProduzidaLiquida', 0) or 0) for r in resultados)
                total_refugado = sum(float(r.get('QuantidadeRefugada', 0) or 0) for r in resultados)
                
                # Soma das quantidades planejadas (agora considerando a operação)
                # Usamos um set para evitar somar a mesma meta várias vezes se ela aparecer em dias diferentes
                # (A lógica de soma de planejado em relatório agrupado é complexa, aqui somamos as linhas visíveis)
                total_planejado = sum(float(r.get('QuantidadePlanejada', 0) or 0) for r in resultados)

                kpis['total_produzido'] = total_produzido
                kpis['total_refugado'] = total_refugado
                producao_bruta_total = total_produzido + total_refugado
                kpis['taxa_refugo_geral'] = (total_refugado / producao_bruta_total * 100) if producao_bruta_total > 0 else 0
                
                # Eficiência simples (Realizado / Planejado das linhas exibidas)
                kpis['eficiencia_geral'] = (total_produzido / total_planejado * 100) if total_planejado > 0 else (100.0 if total_produzido > 0 else 0.0)

                if usa_unidades_caixa:
                    total_caixas_calculado = 0
                    for r in resultados:
                        unidades_por_caixa = r.get('UnidadesPorCaixa')
                        qtd_liq = float(r.get('QuantidadeProduzidaLiquida', 0) or 0)
                        if unidades_por_caixa and unidades_por_caixa > 0 and qtd_liq > 0:
                            total_caixas_calculado += qtd_liq // float(unidades_por_caixa)
                    kpis['total_caixas'] = int(total_caixas_calculado)

                # Gráfico de Tendência
                tendencia_dict = defaultdict(lambda: {'data_obj': None, 'valor': 0.0})
                for r in resultados:
                    data_ref = r.get('DataHoraInicio') 
                    if isinstance(data_ref, date): 
                        if isinstance(data_ref, str):
                            try: data_ref = datetime.strptime(data_ref, '%Y-%m-%d').date()
                            except ValueError: continue
                        dia_iso = data_ref.strftime('%Y-%m-%d')
                        if tendencia_dict[dia_iso]['data_obj'] is None:
                            tendencia_dict[dia_iso]['data_obj'] = data_ref
                        tendencia_dict[dia_iso]['valor'] += float(r.get('QuantidadeProduzidaLiquida', 0) or 0)

                dias_ordenados = sorted(tendencia_dict.values(), key=lambda x: x['data_obj'] if x['data_obj'] else date.min)

                dados_grafico_tendencia = {
                    'labels': [d['data_obj'].strftime('%d/%m') for d in dias_ordenados if d['data_obj']],
                    'data': [d['valor'] for d in dias_ordenados if d['data_obj']]
                }
            else:
                 flash("Nenhum registro de produção encontrado para os filtros selecionados.", "info")

        return render_template("relatorio_producao.html",
                               resultados=resultados, filtros=filtros, maquinas=maquinas,
                               produtos=produtos, operadores=operadores_lista, kpis=kpis,
                               dados_grafico_json=json.dumps(dados_grafico_tendencia, cls=DecimalEncoder),
                               usa_unidades_caixa=usa_unidades_caixa)

    except Exception as e:
        logger.error(f"Erro CRÍTICO em relatorio_producao: {e}", exc_info=True)
        flash(f"Ocorreu um erro ao gerar o relatório.", "error")
        return render_template("relatorio_producao.html",
                               resultados=[], filtros=filtros, maquinas=maquinas or [],
                               produtos=produtos or [], operadores=operadores_lista or [],
                               kpis=kpis, dados_grafico_json='{}', usa_unidades_caixa=False)
    finally:
        if conn_local:
            devolver_conexao(conn_local)
@app.route('/remover_da_fila', methods=['POST'])
@login_requerido
@permissao_requerida('/remover_da_fila') # Assegurar que esta rota tem permissão
def remover_da_fila():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_ordem = request.form.get("id_ordem")
        id_maquina = request.form.get("id_maquina")
        cursor_local.execute("DELETE FROM TBL_FilaOrdem WHERE IDOrdem = ? AND IDMaquina = ?", (id_ordem, id_maquina))
        conn_local.commit()
        flash("Ordem removida da fila.", "success")
        return redirect(url_for('fila_ordens', id_maquina=id_maquina))
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em remover_da_fila: {e}", exc_info=True)
        flash("Ocorreu um erro ao remover da fila.", "error")
        return redirect(url_for('fila_ordens', id_maquina=id_maquina))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/iniciar_op_fila', methods=['GET'])
@login_requerido
@permissao_requerida('/iniciar_op_fila')
def iniciar_op_fila():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_ordem_para_iniciar = request.args.get('id_ordem', type=int)
        id_maquina = request.args.get('id_maquina', type=int)
        id_ordem_operacao = request.args.get('id_ordem_operacao', type=int)

        if not all([id_ordem_para_iniciar, id_maquina, id_ordem_operacao]):
            flash("Erro: Dados incompletos para iniciar a produção.", "error")
            return redirect(url_for('dashboard'))
        
        id_turno = identificar_turno(conn_local, cursor_local)
        id_usuario_logado = session.get('usuario_id')
        cursor_local.execute("SELECT IDOperador FROM TBL_Operador WHERE IDUsuario = ? AND Ativo = 1", id_usuario_logado)
        operador_logado = cursor_local.fetchone()
        id_operador = operador_logado.IDOperador if operador_logado else None

        # ==============================================================================
        # CORREÇÃO: Buscar o ID do Status "Em Execucao" para evitar erro de NULL
        # ==============================================================================
        cursor_local.execute("SELECT IDStatus FROM TBL_StatusOrdemProducao WHERE NomeStatus = 'Em Execucao'")
        status_row = cursor_local.fetchone()
        # Usa o ID encontrado ou 5 como fallback (5 costuma ser 'Em Execucao' no seu sistema)
        id_status_execucao = status_row.IDStatus if status_row else 5 
        # ==============================================================================

        cursor_local.execute("SELECT TOP 1 IDExecucao, IDOrdem, IDOrdemOperacao FROM TBL_ExecucaoOP WHERE IDMaquina = ? AND Status IN ('Em Execucao', 'Em Setup')", (id_maquina,))
        op_em_execucao = cursor_local.fetchone()

        # --- Lógica de Interrupção Automática ---
        if op_em_execucao:
            id_execucao_a_interromper = op_em_execucao.IDExecucao
            id_ordem_a_interromper = op_em_execucao.IDOrdem
            id_operacao_a_interromper = op_em_execucao.IDOrdemOperacao

            if id_operacao_a_interromper != id_ordem_operacao:
                logger.info(f"Máquina {id_maquina} está ocupada. Interrompendo a operação {id_operacao_a_interromper} antes de iniciar a nova.")
                _consumir_estoque_para_ordem(cursor_local, id_ordem_a_interromper, id_execucao_a_interromper)
                
                cursor_local.execute("UPDATE TBL_ExecucaoOP SET DataHoraFim = GETDATE(), Status = 'Interrompido' WHERE IDExecucao = ?", (id_execucao_a_interromper,))
                cursor_local.execute("UPDATE TBL_OrdemProducao SET IDStatus = 3 WHERE IDOrdem = ?", (id_ordem_a_interromper,))
                cursor_local.execute("UPDATE TBL_OrdemProducao_Operacoes SET StatusOperacao = 'Pendente' WHERE IDOrdemOperacao = ?", (id_operacao_a_interromper,))
                
                cursor_local.execute(
                    "INSERT INTO TBL_FilaOrdem (IDMaquina, IDOrdem, StatusFila, OrdemFila, IDOrdemOperacao) VALUES (?, ?, 'pendente', 0, ?)", 
                    (id_maquina, id_ordem_a_interromper, id_operacao_a_interromper)
                )

        cursor_local.execute("""
            SELECT ISNULL(SUM(ev.Quantidade), 0) as QuantidadeAnterior
            FROM VW_EventoProducaoComCicloReal ev
            JOIN TBL_ExecucaoOP ex ON ev.IDExecucao = ex.IDExecucao
            WHERE ex.IDOrdemOperacao = ? AND ev.TipoValor IN ('BOA', 'ESTORNO')
        """, (id_ordem_operacao,))
        resultado_soma = cursor_local.fetchone()
        quantidade_anterior = resultado_soma.QuantidadeAnterior if resultado_soma else 0

        cursor_local.execute("DELETE FROM TBL_FilaOrdem WHERE IDOrdemOperacao = ?", (id_ordem_operacao,))
        reordenar_fila(conn_local, cursor_local, id_maquina)
        
        # Atualiza status da OP e da Operação
        cursor_local.execute("UPDATE TBL_OrdemProducao SET IDStatus = ? WHERE IDOrdem = ?", (id_status_execucao, id_ordem_para_iniciar,))
        cursor_local.execute("UPDATE TBL_OrdemProducao_Operacoes SET StatusOperacao = 'Em Execucao' WHERE IDOrdemOperacao = ?", (id_ordem_operacao,))

        # ==============================================================================
        # CORREÇÃO: Adicionado IDStatus ao INSERT
        # ==============================================================================
        cursor_local.execute("""
            INSERT INTO TBL_ExecucaoOP 
            (IDOrdem, IDMaquina, IDOperador, IDTurno, DataHoraInicio, Status, IDOrdemOperacao, QuantidadeProduzida, IDStatus)
            VALUES (?, ?, ?, ?, GETDATE(), 'Em Execucao', ?, ?, ?)
        """, (id_ordem_para_iniciar, id_maquina, id_operador, id_turno, id_ordem_operacao, quantidade_anterior, id_status_execucao))
        # ==============================================================================
        
        conn_local.commit()
        flash(f"OP iniciada com sucesso! Produção anterior de {float(quantidade_anterior):g} unidades foi mantida.", "success")
        return redirect(url_for('dashboard'))
        
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em iniciar_op_fila: {e}", exc_info=True)
        flash("Ocorreu um erro ao iniciar a OP da fila.", "error")
        return redirect(url_for('dashboard'))
    finally:
        if conn_local: devolver_conexao(conn_local)

# Em planner_app.py, substitua a função salvar_ordem_fila:

@app.route("/salvar_ordem_fila", methods=["POST"])
@login_requerido
@permissao_requerida('/salvar_ordem_fila')
def salvar_ordem_fila():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        ids_fila = request.form.getlist("fila_id")
        posicoes = request.form.getlist("ordem_posicao")

        for id_fila, nova_pos in zip(ids_fila, posicoes):
            # Garante que a posição seja um número inteiro antes de salvar
            posicao_int = int(nova_pos) if nova_pos.isdigit() else 1
            cursor_local.execute("UPDATE TBL_FilaOrdem SET OrdemFila = ? WHERE IDFila = ?", (posicao_int, id_fila))

        conn_local.commit()
        flash("Sequenciamento da fila salvo com sucesso!", "success")
        
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em salvar_ordem_fila: {e}", exc_info=True)
        flash("Ocorreu um erro ao salvar a ordem da fila.", "error")
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
    return redirect(url_for('fila_ordens', id_maquina=request.form.get('id_maquina')))
    
def reordenar_fila(conn_local, cursor_local, id_maquina):
    """
    Reordena a coluna OrdemFila para uma máquina específica usando ROW_NUMBER() do SQL Server.
    É mais eficiente e robusto que o loop em Python.
    """
    try:
        logger.info(f"Reordenando a fila para a máquina ID: {id_maquina} com ROW_NUMBER()")
        
        # Este comando SQL usa uma Common Table Expression (WITH) e a função ROW_NUMBER()
        # para calcular a nova posição de cada item na fila e atualizar todos de uma vez.
        sql_reorder = """
        WITH NovaOrdem AS (
            SELECT 
                IDFila, 
                ROW_NUMBER() OVER (ORDER BY OrdemFila, DataInsercao) AS NovaPosicao
            FROM TBL_FilaOrdem
            WHERE IDMaquina = ?
        )
        UPDATE TBL_FilaOrdem
        SET OrdemFila = NovaOrdem.NovaPosicao
        FROM TBL_FilaOrdem
        JOIN NovaOrdem ON TBL_FilaOrdem.IDFila = NovaOrdem.IDFila;
        """
        
        # Executa o comando de reordenação no banco de dados
        cursor_local.execute(sql_reorder, (id_maquina,))
        
        logger.info(f"Fila para a máquina {id_maquina} reordenada com sucesso via ROW_NUMBER().")
        
    except Exception as e:
        logger.error(f"Erro ao reordenar a fila para a máquina {id_maquina} com ROW_NUMBER(): {e}", exc_info=True)
        # Relança a exceção para que a rota que a chamou possa fazer o rollback.
        raise           
    
@app.route('/registrar_parada', methods=['POST'])
@login_requerido
@permissao_requerida('/registrar_parada')
def registrar_parada():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        data = request.json
        id_maquina = data['id_maquina']
        id_motivo = int(data['id_motivo'])
        correcao_status = bool(data.get('correcao_status', False)) # Variável não utilizada diretamente pela helper, mantida para contexto.

        execucao = obter_info_execucao(id_maquina, conn_local, cursor_local) # Reutiliza a função já refatorada
        if execucao: # Se houver uma OP ativa, indica contexto, mas a máquina ainda está parando.
            logger.warning(f"Máquina {id_maquina} tem OP ativa mas foi registrada parada manual. Verifique se isso é o comportamento desejado.")

        # --- Chamar a função auxiliar para atualizar o status para Parada (Status 0) com o motivo selecionado ---
        _update_machine_status(conn_local, cursor_local, id_maquina, 0, id_motivo, "Parada registrada manualmente pelo usuário")
        # ----------------------------------------------------------------------------------------------------

        conn_local.commit()
        flash("Motivo de parada registrado com sucesso!", "success")
        return jsonify({'mensagem': 'Motivo de parada registrado com sucesso.'})
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em registrar_parada: {e}", exc_info=True)
        flash("Ocorreu um erro ao registrar a parada.", "error")
        return jsonify({'mensagem': str(e)}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# --- ROTAS DE CADASTRO GERAL ---

@app.route('/cadastro_grupo_motivo_refugo', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_grupo_motivo_refugo')
def cadastro_grupo_motivo_refugo():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_grupo = request.args.get('id')
        grupo_editar = None

        if request.method == 'POST':
            id_grupo_form = request.form.get('id_grupo') # Renomeado para não conflitar com id_grupo da URL
            codigo = request.form['codigo']
            nome = request.form['nome']
            descricao = request.form['descricao']
            ativo = 'ativo' in request.form

            if id_grupo_form:
                cursor_local.execute("""
                    UPDATE TBL_GrupoRefugo
                    SET Codigo = ?, NomeGrupo = ?, Descricao = ?, Ativo = ?
                    WHERE IDGrupoMotivoRefugo = ?
                """, codigo, nome, descricao, ativo, id_grupo_form)
                flash("Grupo de motivo de refugo atualizado com sucesso!", "success")
            else:
                cursor_local.execute("""
                    INSERT INTO TBL_GrupoRefugo (Codigo, NomeGrupo, Descricao, Ativo)
                    VALUES (?, ?, ?, ?)
                """, codigo, nome, descricao, ativo)
                flash("Grupo de motivo de refugo cadastrado com sucesso!", "success")

            conn_local.commit()
            return redirect(url_for('cadastro_grupo_motivo_refugo'))

        if id_grupo:
            cursor_local.execute("SELECT * FROM TBL_GrupoRefugo WHERE IDGrupoMotivoRefugo = ?", id_grupo)
            grupo_editar = cursor_local.fetchone()

        cursor_local.execute("SELECT * FROM TBL_GrupoRefugo")
        grupos = cursor_local.fetchall()

        return render_template('cadastro_grupo_motivo_refugo.html', grupos=grupos, grupo_editar=grupo_editar)
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em cadastro_grupo_motivo_refugo: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar grupos de refugo.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/cadastro_motivo_refugo', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_motivo_refugo')
def cadastro_motivo_refugo():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_edicao = request.args.get('id')
        motivo_editar = None

        if request.method == 'POST':
            id_motivo = request.form.get('id_motivo')
            codigo = request.form['codigo']
            descricao = request.form['descricao']
            id_grupo = request.form['id_grupo']
            ativo = 1 if 'ativo' in request.form else 0
            
            # CORREÇÃO: Lendo o valor do checkbox com o nome correto 'subtrai_da_producao'
            subtrai_da_producao = 1 if 'subtrai_da_producao' in request.form else 0

            if id_motivo:
                # CORREÇÃO: Usando a coluna 'SubtraiDaProducao' no UPDATE
                cursor_local.execute("""
                    UPDATE TBL_MotivoRefugo
                    SET Codigo = ?, Descricao = ?, IDGrupoMotivoRefugo = ?, Ativo = ?, SubtraiDaProducao = ?
                    WHERE IDMotivoRefugo = ?
                """, (codigo, descricao, id_grupo, ativo, subtrai_da_producao, id_motivo))
                flash("Motivo de refugo atualizado com sucesso!", "success")
            else:
                # CORREÇÃO: Usando a coluna 'SubtraiDaProducao' no INSERT
                cursor_local.execute("""
                    INSERT INTO TBL_MotivoRefugo (Codigo, Descricao, IDGrupoMotivoRefugo, Ativo, SubtraiDaProducao)
                    VALUES (?, ?, ?, ?, ?)
                """, (codigo, descricao, id_grupo, ativo, subtrai_da_producao))
                flash("Motivo de refugo cadastrado com sucesso!", "success")

            conn_local.commit()
            return redirect(url_for('cadastro_motivo_refugo'))

        if id_edicao:
            # O SELECT * já buscará a nova coluna SubtraiDaProducao
            cursor_local.execute("SELECT * FROM TBL_MotivoRefugo WHERE IDMotivoRefugo = ?", id_edicao)
            motivo_editar = cursor_local.fetchone()

        cursor_local.execute("SELECT * FROM TBL_GrupoRefugo WHERE Ativo = 1")
        grupos = cursor_local.fetchall()

        # O SELECT M.* já buscará a nova coluna SubtraiDaProducao
        cursor_local.execute("""
            SELECT M.*, G.NomeGrupo
            FROM TBL_MotivoRefugo M
            LEFT JOIN TBL_GrupoRefugo G ON M.IDGrupoMotivoRefugo = G.IDGrupoMotivoRefugo
            ORDER BY M.Descricao
        """)
        motivos = cursor_local.fetchall()

        return render_template('cadastro_motivo_refugo.html', motivos=motivos, motivo_editar=motivo_editar, grupos=grupos)
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em cadastro_motivo_refugo: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar motivos de refugo.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            devolver_conexao(conn_local)

@app.route('/modelagem')
@login_requerido
@permissao_requerida('/modelagem')
def modelagem():
    return render_template('modelagem.html')

@app.route('/cadastro_empresa', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_empresa')
def cadastro_empresa():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_edicao = request.args.get('id')
        empresa_editar = None

        if request.method == 'POST':
            id_empresa_form = request.form.get('id_empresa')
            nome = request.form['nome']
            codigo = request.form['codigo']
            descricao = request.form['descricao']
            ativo = 1 if 'ativo' in request.form else 0

            if id_empresa_form:
                # Lógica de ATUALIZAÇÃO
                cursor_local.execute("""
                    UPDATE TBL_Empresa
                    SET Nome = ?, Codigo = ?, Descricao = ?, Ativo = ?
                    WHERE IDEmpresa = ?
                """, (nome, codigo, descricao, ativo, id_empresa_form))
                flash("Empresa atualizada com sucesso!", "success")
            else:
                # Lógica de CRIAÇÃO
                cursor_local.execute("""
                    INSERT INTO TBL_Empresa (Nome, Codigo, Descricao, Ativo, DtCriacao)
                    VALUES (?, ?, ?, ?, GETDATE())
                """, (nome, codigo, descricao, ativo))
                flash("Empresa cadastrada com sucesso!", "success")
            
            conn_local.commit()
            return redirect(url_for('cadastro_empresa'))

        # Lógica GET para carregar a página
        if id_edicao:
            cursor_local.execute("SELECT * FROM TBL_Empresa WHERE IDEmpresa = ?", id_edicao)
            empresa_editar = cursor_local.fetchone()

        cursor_local.execute("SELECT IDEmpresa, Nome, Codigo, Descricao, Ativo FROM TBL_Empresa")
        empresas = cursor_local.fetchall()

        return render_template('cadastro_empresa.html', empresas=empresas, empresa=empresa_editar)

    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em cadastro_empresa: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar empresas.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/cadastro_setor', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_setor')
def cadastro_setor():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_edicao = request.args.get('id')
        setor_editar = None
        
        if request.method == 'POST':
            # Corrigido para pegar 'id_setor' do formulário
            id_setor_form = request.form.get('id_setor')
            nome = request.form['nome']
            codigo = request.form['codigo']
            descricao = request.form['descricao']
            ativo = 1 if 'ativo' in request.form else 0
            id_empresa = request.form['id_empresa']
            id_area = request.form['id_area']

            if id_setor_form:
                # Lógica de ATUALIZAÇÃO
                cursor_local.execute("""
                    UPDATE TBL_Setor 
                    SET Nome = ?, Codigo = ?, Descricao = ?, Ativo = ?, IDEmpresa = ?, IDArea = ?
                    WHERE IDSetor = ?
                """, (nome, codigo, descricao, ativo, id_empresa, id_area, id_setor_form))
                flash("Setor atualizado com sucesso!", "success")
            else:
                # Lógica de CRIAÇÃO
                cursor_local.execute("""
                    INSERT INTO TBL_Setor (Nome, Codigo, Descricao, Ativo, DtCriacao, IDEmpresa, IDArea)
                    VALUES (?, ?, ?, ?, GETDATE(), ?, ?)
                """, (nome, codigo, descricao, ativo, id_empresa, id_area))
                flash("Setor cadastrado com sucesso!", "success")
            
            conn_local.commit()
            return redirect(url_for('cadastro_setor'))

        # Lógica GET para carregar a página
        if id_edicao:
            cursor_local.execute("SELECT * FROM TBL_Setor WHERE IDSetor = ?", (id_edicao,))
            setor_editar = cursor_local.fetchone()

        cursor_local.execute("""
            SELECT S.IDSetor, S.Nome, S.Codigo, S.Descricao, S.Ativo, 
                   S.IDEmpresa, E.Nome AS NomeEmpresa,
                   S.IDArea, A.Nome AS NomeArea
            FROM TBL_Setor S
            LEFT JOIN TBL_Empresa E ON S.IDEmpresa = E.IDEmpresa
            LEFT JOIN TBL_Area A ON S.IDArea = A.IDArea
            ORDER BY S.Nome
        """)
        setores = cursor_local.fetchall()

        cursor_local.execute("SELECT IDEmpresa, Nome FROM TBL_Empresa WHERE Ativo = 1 ORDER BY Nome")
        empresas = cursor_local.fetchall()

        cursor_local.execute("SELECT IDArea, Nome, IDEmpresa FROM TBL_Area WHERE Ativo = 1 ORDER BY Nome")
        areas = cursor_local.fetchall()
        
        return render_template('cadastro_setor.html', 
                              setores=setores, 
                              empresas=empresas, 
                              areas=areas,
                              setor=setor_editar) # Passa o setor para o template com a chave 'setor'
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em cadastro_setor: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar setores.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/cadastro_area', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_area')
def cadastro_area():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_edicao = request.args.get('id')
        area_editar = None

        if request.method == 'POST':
            id_area_form = request.form.get('id_area')
            nome = request.form['nome']
            codigo = request.form['codigo']
            descricao = request.form['descricao']
            ativo = 1 if 'ativo' in request.form else 0
            id_empresa = request.form['id_empresa']

            if id_area_form:
                # Lógica de ATUALIZAÇÃO
                cursor_local.execute("""
                    UPDATE TBL_Area
                    SET Nome = ?, Codigo = ?, Descricao = ?, Ativo = ?, IDEmpresa = ?
                    WHERE IDArea = ?
                """, (nome, codigo, descricao, ativo, id_empresa, id_area_form))
                flash("Área atualizada com sucesso!", "success")
            else:
                # Lógica de CRIAÇÃO
                cursor_local.execute("""
                    INSERT INTO TBL_Area (Nome, Codigo, Descricao, Ativo, DtCriacao, IDEmpresa)
                    VALUES (?, ?, ?, ?, GETDATE(), ?)
                """, (nome, codigo, descricao, ativo, id_empresa))
                flash("Área cadastrada com sucesso!", "success")

            conn_local.commit()
            return redirect(url_for('cadastro_area'))

        # Lógica GET para carregar a página
        if id_edicao:
            cursor_local.execute("SELECT * FROM TBL_Area WHERE IDArea = ?", id_edicao)
            area_editar = cursor_local.fetchone()

        cursor_local.execute("""
            SELECT A.IDArea, A.Nome, A.Codigo, A.Descricao, A.Ativo, A.IDEmpresa, E.Nome AS NomeEmpresa
            FROM TBL_Area A
            LEFT JOIN TBL_Empresa E ON A.IDEmpresa = E.IDEmpresa
            ORDER BY A.Nome
        """)
        areas = cursor_local.fetchall()

        cursor_local.execute("SELECT IDEmpresa, Nome FROM TBL_Empresa WHERE Ativo = 1 ORDER BY Nome")
        empresas = cursor_local.fetchall()

        return render_template('cadastro_area.html', areas=areas, empresas=empresas, area=area_editar)
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em cadastro_area: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar áreas.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/cadastro_grupo_parada', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_grupo_parada')
def cadastro_grupo_parada():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_grupo = request.args.get('id')
        grupo_editar = None

        if request.method == 'POST':
            # Captura o novo campo 'codigo' e o ID do formulário
            id_grupo_form = request.form.get('id_grupo_form')
            codigo = request.form['codigo']
            nome = request.form['nome']
            descricao = request.form['descricao']
            ativo = 'ativo' in request.form

            if id_grupo_form:
                # Lógica de ATUALIZAÇÃO com o novo campo
                cursor_local.execute("""
                    UPDATE TBL_GrupoParada
                    SET Codigo = ?, NomeGrupo = ?, Descricao = ?, Ativo = ?
                    WHERE IDGrupoParada = ?
                """, (codigo, nome, descricao, ativo, id_grupo_form))
                flash("Grupo de parada atualizado com sucesso!", "success")
            else:
                # Lógica de CRIAÇÃO com o novo campo
                cursor_local.execute("""
                    INSERT INTO TBL_GrupoParada (Codigo, NomeGrupo, Descricao, Ativo)
                    VALUES (?, ?, ?, ?)
                """, (codigo, nome, descricao, ativo))
                flash("Grupo de parada cadastrado com sucesso!", "success")
            
            conn_local.commit()
            return redirect(url_for('cadastro_grupo_parada'))

        # Lógica GET para carregar a página
        if id_grupo:
            cursor_local.execute("SELECT * FROM TBL_GrupoParada WHERE IDGrupoParada = ?", id_grupo)
            grupo_editar = cursor_local.fetchone()

        # A query SELECT * já busca a nova coluna 'Codigo' automaticamente
        cursor_local.execute("SELECT * FROM TBL_GrupoParada ORDER BY NomeGrupo")
        grupos = cursor_local.fetchall()

        return render_template('cadastro_grupo_parada.html', grupos=grupos, grupo_editar=grupo_editar)
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em cadastro_grupo_parada: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar grupos de parada.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
    
def obter_motivo_parada(id_maquina, conn_local, cursor_local):
    """
    Obtém o motivo de parada atual de uma máquina.
    Recebe conn_local e cursor_local.
    """
    try:
        cursor_local.execute("""
            SELECT TOP 1 SM.IDMotivoParada, MP.Descricao
            FROM TBL_StatusMaquina SM
            LEFT JOIN TBL_MotivoParada MP ON SM.IDMotivoParada = MP.IDMotivoParada
            WHERE SM.IDMaquina = ? 
            AND SM.Status = 0
            AND SM.DataHoraFim IS NULL
            ORDER BY SM.DataHoraRegistro DESC
        """, id_maquina)
        
        motivo = cursor_local.fetchone()
        
        if motivo and motivo[0]:
            return {
                'id': motivo[0],
                'descricao': motivo[1] if motivo[1] else "Motivo não especificado"
            }
        else:
            return {
                'id': None,
                'descricao': "Parada não identificada"
            }
            
    except Exception as e:
        logger.error(f"Erro ao obter motivo de parada: {str(e)}", exc_info=True)
        return {
            'id': None,
            'descricao': "Erro ao obter motivo"
        }    
        
@app.route('/cadastro_motivo_parada', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_motivo_parada')
def cadastro_motivo_parada():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_motivo = request.args.get('id')
        motivo_editar = None

        if request.method == 'POST':
            id_motivo_form = request.form.get('id_motivo')
            codigo = request.form.get('codigo', '').strip().upper()
            descricao = request.form.get('descricao', '').strip()
            planejada = int(request.form.get('planejada'))
            id_grupo = request.form.get('id_grupo')
            ativo = 1 if 'ativo' in request.form else 0
            retorno_automatico = 1 if 'retorno_automatico' in request.form else 0
            contar_pecas = 1 if 'contar_pecas' in request.form else 0
            
            # --- NOVO CAMPO ---
            comentario_obrigatorio = 1 if 'comentario_obrigatorio' in request.form else 0
            # ------------------

            tempo_limite_minutos_str = request.form.get('tempo_limite')
            tempo_limite_minutos_db = None
            if planejada == 1 and tempo_limite_minutos_str and tempo_limite_minutos_str.isdigit():
                tempo_limite_minutos_db = int(tempo_limite_minutos_str)

            if id_motivo_form and id_motivo_form.isdigit():
                # --- UPDATE ATUALIZADO ---
                cursor_local.execute("""
                    UPDATE TBL_MotivoParada
                    SET Codigo = ?, Descricao = ?, FlgPlanejada = ?, Ativo = ?, IDGrupoParada = ?,
                        RetornoAutomaticoProducao = ?, ContarPecasNaParada = ?, TempoLimiteMinutos = ?,
                        ComentarioObrigatorio = ?
                    WHERE IDMotivoParada = ?
                """, (codigo, descricao, planejada, ativo, id_grupo, retorno_automatico, contar_pecas, tempo_limite_minutos_db, comentario_obrigatorio, id_motivo_form))
                flash("Motivo de parada atualizado com sucesso!", "success")
            else:
                # --- INSERT ATUALIZADO ---
                cursor_local.execute("""
                    INSERT INTO TBL_MotivoParada 
                    (Codigo, Descricao, FlgPlanejada, Ativo, IDGrupoParada, RetornoAutomaticoProducao, ContarPecasNaParada, TempoLimiteMinutos, ComentarioObrigatorio)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (codigo, descricao, planejada, ativo, id_grupo, retorno_automatico, contar_pecas, tempo_limite_minutos_db, comentario_obrigatorio))
                flash("Motivo de parada cadastrado com sucesso!", "success")

            conn_local.commit()
            return redirect(url_for('cadastro_motivo_parada'))

        if id_motivo:
            cursor_local.execute("SELECT * FROM TBL_MotivoParada WHERE IDMotivoParada = ?", id_motivo)
            motivo_editar = cursor_local.fetchone()

        cursor_local.execute("SELECT IDGrupoParada, NomeGrupo FROM TBL_GrupoParada WHERE Ativo = 1 ORDER BY NomeGrupo")
        grupos = cursor_local.fetchall()

        cursor_local.execute("""
            SELECT M.*, G.NomeGrupo
            FROM TBL_MotivoParada M
            LEFT JOIN TBL_GrupoParada G ON M.IDGrupoParada = G.IDGrupoParada
            ORDER BY M.Codigo
        """)
        motivos = cursor_local.fetchall()

        return render_template('cadastro_motivo_parada.html', 
                               motivos=motivos, 
                               motivo_editar=motivo_editar, 
                               grupos=grupos)
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em cadastro_motivo_parada: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar motivos de parada.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/cadastro_turno', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_turno')
def cadastro_turno():
    conn_local = None
    # Variável de resposta para garantir o fluxo correto
    response = None
    
    try:
        conn_local = obter_conexao() 
        cursor_local = conn_local.cursor()

        id_turno = request.args.get('id')
        turno_editar = None

        if request.method == 'POST':
            id_turno_form = request.form.get('id_turno')
            codigo = request.form['codigo']
            nome = request.form['nome']
            hora_inicio = request.form['hora_inicio']
            hora_fim = request.form['hora_fim']
            
            # Captura dos dias da semana
            dom = 1 if 'dom' in request.form else 0
            seg = 1 if 'seg' in request.form else 0
            ter = 1 if 'ter' in request.form else 0
            qua = 1 if 'qua' in request.form else 0
            qui = 1 if 'qui' in request.form else 0
            sex = 1 if 'sex' in request.form else 0
            sab = 1 if 'sab' in request.form else 0
            todos = 1 if 'todos' in request.form else 0
            
            inicia_dia_anterior = 1 if 'inicia_dia_anterior' in request.form else 0
            ativo = 1 if 'ativo' in request.form else 0

            if id_turno_form and id_turno_form.isdigit():
                cursor_local.execute("""
                    UPDATE TBL_Turno SET Codigo = ?, NomeTurno = ?, HoraInicio = ?, HoraFim = ?,
                           Dom = ?, Seg = ?, Ter = ?, Qua = ?, Qui = ?, Sex = ?, Sab = ?, Todos = ?,
                           IniciaDiaAnterior = ?, Ativo = ?
                    WHERE IDTurno = ?
                """, (codigo, nome, hora_inicio, hora_fim, dom, seg, ter, qua, qui, sex, sab, todos,
                      inicia_dia_anterior, ativo, id_turno_form))
                flash("Turno atualizado com sucesso! A agenda das máquinas será recalculada.", "success")
                
                # ID para o flattener usar
                id_turno_afetado = id_turno_form
            else:
                cursor_local.execute("""
                    INSERT INTO TBL_Turno (Codigo, NomeTurno, HoraInicio, HoraFim, Dom, Seg, Ter, Qua, Qui, Sex, Sab, Todos, IniciaDiaAnterior, Ativo)
                    OUTPUT INSERTED.IDTurno
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (codigo, nome, hora_inicio, hora_fim, dom, seg, ter, qua, qui, sex, sab, todos, inicia_dia_anterior, ativo))
                
                id_novo = cursor_local.fetchone()[0]
                flash("Turno cadastrado com sucesso! A agenda das máquinas será gerada.", "success")
                
                # ID para o flattener usar
                id_turno_afetado = id_novo

            conn_local.commit()

            # --- INTEGRAÇÃO COM FLATTENER (AGENDA CONSOLIDADA) ---
            # Importa aqui para evitar ciclos no topo do arquivo se o flattener importar o app
            try:
                from flattener import consolidar_agendas_afetadas
                
                # Roda em background para não deixar o usuário esperando o cálculo
                # Passamos o ID do turno para ele recalcular apenas as máquinas deste turno
                thread_flattener = threading.Thread(
                    target=consolidar_agendas_afetadas, 
                    args=(id_turno_afetado, None)
                )
                thread_flattener.start()
                logger.info(f"Disparado recálculo de agenda para o Turno ID {id_turno_afetado}")
                
            except ImportError:
                logger.error("Erro: Módulo 'flattener' não encontrado. A agenda não foi atualizada.")
            except Exception as e_flat:
                logger.error(f"Erro ao disparar flattener: {e_flat}")
            # -----------------------------------------------------

            response = redirect(url_for('cadastro_turno'))
            
        else: # Lógica para GET
            if id_turno:
                cursor_local.execute("SELECT * FROM TBL_Turno WHERE IDTurno = ?", id_turno)
                turno_editar = cursor_local.fetchone()

            cursor_local.execute("SELECT * FROM TBL_Turno ORDER BY NomeTurno")
            turnos = cursor_local.fetchall()

            response = render_template('cadastro_turno.html', turnos=turnos, turno_editar=turno_editar)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em cadastro_turno: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar turnos.", "error")
        response = redirect(url_for('home')) 
    finally:
        if conn_local:
            devolver_conexao(conn_local)

    return response
    
#####TELA PRODUÇÃO
@app.route('/cadastro_producao')
@login_requerido
@permissao_requerida('/cadastro_producao')
def cadastro_producao():
    return render_template('cadastro_producao.html')
    
#### relatorios
@app.route('/relatorios')
@login_requerido
@permissao_requerida('/relatorios')
def relatorios():
    return render_template('relatorios.html')

def validar_data(data_str):
    try:
        return datetime.strptime(data_str, '%Y-%m-%d')
    except ValueError: # Captura erro específico para formato de data
        return None

@app.route('/relatorio_refugos', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relatorio_refugos')
def relatorio_refugos():
    conn_local = None
    agrupado = []
    dados_pareto = {} 
    kpis = {'total_refugado': 0}

    data_fim_padrao = datetime.now().strftime('%Y-%m-%d')
    data_inicio_padrao = (datetime.now() - timedelta(days=7)).strftime('%Y-%m-%d')
    
    filtros = {
        "data_inicio": request.form.get("data_inicio", data_inicio_padrao),
        "data_fim": request.form.get("data_fim", data_fim_padrao),
        "codigo_ordem": request.form.get("codigo_ordem")
    }

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            # 1. Parseia as datas do filtro
            data_inicio_dt = validar_data(filtros["data_inicio"])
            data_fim_dt = validar_data(filtros["data_fim"])

            # 2. Define o CTE base
            base_cte = """
                WITH EventosComDataTurno AS (
                    SELECT 
                        E.*, T.NomeTurno, T.IniciaDiaAnterior, T.HoraInicio AS HoraInicioTurno,
                        CASE
                            WHEN T.IniciaDiaAnterior = 1 AND CAST(E.DataHoraEvento AS TIME) < CAST(T.HoraInicio AS TIME)
                            THEN CAST(DATEADD(day, -1, E.DataHoraEvento) AS DATE)
                            ELSE CAST(E.DataHoraEvento AS DATE)
                        END AS DataReferenciaTurno
                    FROM VW_EventoProducaoComCicloReal E
                    LEFT JOIN TBL_Turno T ON E.IDTurno = T.IDTurno
                    WHERE E.TipoValor = 'REFUGO'
                )
            """
            
            # 3. Define o FROM e o WHERE clause
            from_where_clause = """
                FROM EventosComDataTurno EVT
                JOIN TBL_ExecucaoOP EX ON EX.IDExecucao = EVT.IDExecucao
                JOIN TBL_OrdemProducao O ON O.IDOrdem = EX.IDOrdem
                JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
                JOIN TBL_Recurso R ON R.IDMaquina = EX.IDMaquina
                LEFT JOIN TBL_MotivoRefugo MR ON MR.IDMotivoRefugo = EVT.IDMotivoRefugo
                WHERE EVT.DataReferenciaTurno BETWEEN ? AND ?
            """
            params = [data_inicio_dt, data_fim_dt]
            
            if filtros["codigo_ordem"]: 
                from_where_clause += " AND O.CodigoOrdem = ?"
                params.append(filtros["codigo_ordem"])

            # 4. Query de Detalhes (COM A COLUNA OBSERVAÇÃO)
            query_detalhes = base_cte + f"""
                SELECT EVT.DataHoraEvento, R.NomeMaquina, EVT.Quantidade, 
                       MR.Descricao AS MotivoRefugo, O.CodigoOrdem, P.CodigoProduto, P.NomeProduto,
                       EVT.ObsEvento -- << CAMPO ADICIONADO
                {from_where_clause}
            """
            cursor_local.execute(query_detalhes, params)
            refugos_raw = cursor_local.fetchall()
            
            agrupado_dict = defaultdict(lambda: {'ordem': '', 'produto': '', 'total_qtde': 0, 'refugos': []})
            for row in refugos_raw:
                chave = (row.CodigoOrdem, f"{row.CodigoProduto} - {row.NomeProduto}")
                agrupado_dict[chave]['ordem'] = row.CodigoOrdem
                agrupado_dict[chave]['produto'] = f"{row.CodigoProduto} - {row.NomeProduto}"
                agrupado_dict[chave]['refugos'].append(row)
                agrupado_dict[chave]['total_qtde'] += row.Quantidade
            agrupado = list(agrupado_dict.values())

            # 5. Query do Pareto (sem alterações necessárias, pois agrupa por motivo)
            query_pareto = base_cte + f"""
                SELECT ISNULL(MR.Descricao, 'Não Classificado') as Motivo, SUM(EVT.Quantidade) as TotalQuantidade
                {from_where_clause}
                GROUP BY ISNULL(MR.Descricao, 'Não Classificado')
                ORDER BY TotalQuantidade DESC
            """
            cursor_local.execute(query_pareto, params)
            pareto_raw = cursor_local.fetchall()
            
            if pareto_raw:
                total_geral_refugado = sum(p.TotalQuantidade for p in pareto_raw)
                kpis['total_refugado'] = total_geral_refugado
                labels = [p.Motivo for p in pareto_raw]
                data_bar = [float(p.TotalQuantidade) for p in pareto_raw]
                acumulado = 0
                data_line = []
                for p in pareto_raw:
                    acumulado += p.TotalQuantidade
                    data_line.append((acumulado / total_geral_refugado) * 100)
                dados_pareto = {'labels': labels, 'data_bar': data_bar, 'data_line': data_line}

        return render_template('relatorio_refugos.html', 
                               agrupado=agrupado, 
                               dados_pareto_json=json.dumps(dados_pareto, cls=DecimalEncoder), 
                               kpis=kpis,
                               data_inicio_padrao=filtros["data_inicio"],
                               data_fim_padrao=filtros["data_fim"])
    except Exception as e:
        logger.error(f"Erro em relatorio_refugos: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerar o relatório de refugos.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/api/motivos-alarme')
@login_requerido
def api_motivos_alarme():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # --- INÍCIO DA ALTERAÇÃO ---
        # Adiciona a nova coluna 'ComentarioObrigatorio' ao SELECT
        cursor_local.execute("""
            SELECT IDMotivoAlarme, Codigo, Nome, TipoAlarme, ComentarioObrigatorio
            FROM TBL_MotivoAlarme
            WHERE Ativo = 1
            ORDER BY TipoAlarme, Nome
        """)
        # --- FIM DA ALTERAÇÃO ---
        rows = cursor_local.fetchall()
        
        motivos_corrigidos = []
        for row in rows:
            motivos_corrigidos.append({
                'IDMotivoAlarme': row.IDMotivoAlarme,
                'Codigo': row.Codigo,
                'Nome': row.Nome,
                'TipoAlarme': row.TipoAlarme,
                # --- INÍCIO DA ALTERAÇÃO ---
                # Adiciona o novo campo ao dicionário JSON que será enviado
                'ComentarioObrigatorio': bool(row.ComentarioObrigatorio)
                # --- FIM DA ALTERAÇÃO ---
            })
        return jsonify(motivos_corrigidos)

    except Exception as e:
        logger.error(f"Erro em /api/motivos-alarme: {e}", exc_info=True)
        return jsonify({"error": "Falha ao buscar dados"}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# Rota que recebe os dados do modal e dispara o alarme
@app.route('/api/disparar-alarme-manual', methods=['POST'])
@login_requerido
def api_disparar_alarme_manual():
    data = request.json
    try:
        id_motivo = int(data.get('id_motivo_alarme'))
        id_maquina = int(data.get('id_maquina'))
        observacao = data.get('observacao', '')

        disparar_alarme(
            id_motivo_alarme=id_motivo,
            tipo_disparo='Manual',
            id_maquina=id_maquina,
            id_usuario_contexto=session.get('usuario_id'),
            observacao=observacao
        )
        return jsonify({'success': True})
    except Exception as e:
        logger.error(f"Erro em /api/disparar-alarme-manual: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Erro interno no servidor.'}), 500
        
def disparar_alarme(id_motivo_alarme, tipo_disparo, id_maquina=None, id_motivo_parada_gatilho=None, id_usuario_contexto=None, observacao='', enviar_email=True):
    """
    Função central para registrar e notificar um alarme.
    VERSÃO ATUALIZADA: Verifica se o alarme exige reconhecimento.
    """
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # --- INÍCIO DA ALTERAÇÃO ---
        # 1. Busca a configuração do motivo do alarme
        cursor_local.execute("SELECT ExigeReconhecimento FROM TBL_MotivoAlarme WHERE IDMotivoAlarme = ?", (id_motivo_alarme,))
        motivo_alarme_info = cursor_local.fetchone()

        # 2. Define o status inicial com base na configuração
        status_inicial = 'ATIVO'
        if motivo_alarme_info and not motivo_alarme_info.ExigeReconhecimento:
            status_inicial = 'AUTO_CONCLUIDO' # Um novo status para não aparecer na tela
        # --- FIM DA ALTERAÇÃO ---
        
        # 3. Insere o log já com o status correto
        cursor_local.execute("""
            INSERT INTO TBL_LogAlarmes 
            (IDMotivoAlarme, TipoDisparo, IDUsuarioDisparo, IDMotivoParadaGatilho, Observacao, IDMaquina, Status)
            OUTPUT INSERTED.IDLogAlarme
            VALUES (?, ?, ?, ?, ?, ?, ?)
        """, (id_motivo_alarme, tipo_disparo, id_usuario_contexto, id_motivo_parada_gatilho, observacao, id_maquina, status_inicial))
        
        id_log_alarme = cursor_local.fetchone()[0]
        conn_local.commit()
        logger.info(f"Alarme ID {id_log_alarme} (Status: {status_inicial}) registrado para a máquina ID {id_maquina}.")

        if enviar_email:
            thread_email = threading.Thread(target=enviar_notificacao_email, args=(id_log_alarme,))
            thread_email.start()
        
        # A notificação visual só é necessária se o alarme for ativo
        if status_inicial == 'ATIVO':
            notificar_dashboard_visual(id_log_alarme)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"ERRO CRÍTICO na função central disparar_alarme: {e}", exc_info=True)
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# Em planner_app.py

def enviar_notificacao_email(id_log_alarme):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        cursor_local.execute("""
            SELECT 
                L.IDLogAlarme, L.DataHoraOcorrencia, L.Observacao, L.IDMotivoAlarme,
                MA.Nome AS NomeAlarme, MA.TipoAlarme,
                U.NomeUsuario AS NomeUsuarioDisparo,
                R.NomeMaquina,
                ExecInfo.CodigoOrdem,
                ExecInfo.NomeProduto,
                ExecInfo.NomeOperador
            FROM TBL_LogAlarmes L
            JOIN TBL_MotivoAlarme MA ON L.IDMotivoAlarme = MA.IDMotivoAlarme
            LEFT JOIN TBL_Usuario U ON L.IDUsuarioDisparo = U.IDUsuario
            LEFT JOIN TBL_Recurso R ON L.IDMaquina = R.IDMaquina
            OUTER APPLY (
                SELECT TOP 1 OP.CodigoOrdem, P.NomeProduto, Opr.NomeOperador
                FROM TBL_ExecucaoOP EX
                JOIN TBL_OrdemProducao OP ON EX.IDOrdem = OP.IDOrdem
                JOIN TBL_Produto P ON OP.IDProduto = P.IDProduto
                LEFT JOIN TBL_Operador Opr ON EX.IDOperador = Opr.IDOperador
                WHERE EX.IDMaquina = L.IDMaquina AND L.DataHoraOcorrencia >= EX.DataHoraInicio AND (L.DataHoraOcorrencia < EX.DataHoraFim OR EX.DataHoraFim IS NULL)
                ORDER BY EX.DataHoraInicio DESC
            ) AS ExecInfo
            WHERE L.IDLogAlarme = ?
        """, (id_log_alarme,))
        alarme = cursor_local.fetchone()

        if not alarme:
            logger.warning(f"Não foi possível encontrar detalhes para o Log de Alarme ID {id_log_alarme}.")
            return

        cursor_local.execute("""
            SELECT DISTINCT U.Email
            FROM TBL_Usuario U
            JOIN TBL_AlarmeGrupoUsuario AGU ON U.IDGrupo = AGU.IDGrupo
            WHERE AGU.IDMotivoAlarme = ? AND U.Ativo = 1 AND U.Email IS NOT NULL AND U.Email <> ''
        """, (alarme.IDMotivoAlarme,))
        destinatarios = [row.Email for row in cursor_local.fetchall()]

        if not destinatarios:
            logger.info(f"Nenhum destinatário de e-mail encontrado para o alarme '{alarme.NomeAlarme}'.")
            return

        # --- ALTERAÇÃO 1: Busca a nova chave 'SMTP_SENDER_NAME' ---
        config_keys = "('SMTP_HOST', 'SMTP_PORT', 'SMTP_USER', 'SMTP_PASSWORD', 'SMTP_USE_TLS', 'SMTP_SENDER_EMAIL', 'SMTP_SENDER_NAME')"
        cursor_local.execute(f"SELECT ChaveConfig, ValorConfig FROM TBL_Configuracao WHERE ChaveConfig IN {config_keys}")
        smtp_config_raw = cursor_local.fetchall()
        smtp_config = {row.ChaveConfig: row.ValorConfig for row in smtp_config_raw}

        msg = MIMEMultipart()
        
        # --- ALTERAÇÃO 2: Formata o cabeçalho 'From' com nome e e-mail ---
        sender_name = smtp_config.get('SMTP_SENDER_NAME', 'Planner Alertas')
        sender_email = smtp_config.get('SMTP_SENDER_EMAIL')
        msg['From'] = formataddr((sender_name, sender_email))

        msg['To'] = ", ".join(destinatarios)
        msg['Subject'] = f"ALERTA: {alarme.TipoAlarme} - {alarme.NomeAlarme} em {alarme.NomeMaquina or 'Recurso não definido'}"

        body_html = f"""
        <html>
            <body style="font-family: Arial, sans-serif; line-height: 1.6;">
                <h2 style="color: #c62828;">Notificação de Alarme do Sistema Planner</h2>
                <p>Um novo alarme foi registrado no sistema:</p>
                <table style="width: 100%; border-collapse: collapse;">
                    <tr style="background-color: #f2f2f2;">
                        <td style="padding: 8px; border: 1px solid #ddd; width: 30%;"><strong>Recurso (Máquina):</strong></td>
                        <td style="padding: 8px; border: 1px solid #ddd;"><strong>{alarme.NomeMaquina or 'Não especificada'}</strong></td>
                    </tr>
                    <tr>
                        <td style="padding: 8px; border: 1px solid #ddd;"><strong>Operador:</strong></td>
                        <td style="padding: 8px; border: 1px solid #ddd;">{alarme.NomeOperador or 'Nenhum operador associado'}</td>
                    </tr>
                    <tr style="background-color: #f2f2f2;">
                        <td style="padding: 8px; border: 1px solid #ddd;"><strong>Alarme:</strong></td>
                        <td style="padding: 8px; border: 1px solid #ddd;">{alarme.NomeAlarme}</td>
                    </tr>
                    <tr>
                        <td style="padding: 8px; border: 1px solid #ddd;"><strong>Ordem de Produção:</strong></td>
                        <td style="padding: 8px; border: 1px solid #ddd;">{alarme.CodigoOrdem or 'Nenhuma OP ativa'}</td>
                    </tr>
                    <tr style="background-color: #f2f2f2;">
                        <td style="padding: 8px; border: 1px solid #ddd;"><strong>Produto:</strong></td>
                        <td style="padding: 8px; border: 1px solid #ddd;">{alarme.NomeProduto or 'Nenhum produto em produção'}</td>
                    </tr>
                    <tr>
                        <td style="padding: 8px; border: 1px solid #ddd;"><strong>Data e Hora:</strong></td>
                        <td style="padding: 8px; border: 1px solid #ddd;">{alarme.DataHoraOcorrencia.strftime('%d/%m/%Y %H:%M:%S')}</td>
                    </tr>
                    <tr style="background-color: #f2f2f2;">
                        <td style="padding: 8px; border: 1px solid #ddd;"><strong>Observação:</strong></td>
                        <td style="padding: 8px; border: 1px solid #ddd;">{alarme.Observacao or 'Nenhuma'}</td>
                    </tr>
                </table>
                <p style="font-size: 0.8em; color: #777;">Este é um e-mail automático. Por favor, não responda.</p>
            </body>
        </html>
        """
        msg.attach(MIMEText(body_html, 'html'))

        server = smtplib.SMTP(smtp_config.get('SMTP_HOST'), int(smtp_config.get('SMTP_PORT')))
        if smtp_config.get('SMTP_USE_TLS', 'false').lower() == 'true':
            server.starttls()
        server.login(smtp_config.get('SMTP_USER'), smtp_config.get('SMTP_PASSWORD'))
        server.sendmail(smtp_config.get('SMTP_SENDER_EMAIL'), destinatarios, msg.as_string())
        server.quit()

        logger.info(f"E-mail de notificação para o alarme '{alarme.NomeAlarme}' enviado para {len(destinatarios)} destinatário(s).")

    except Exception as e:
        logger.error(f"Falha ao enviar e-mail de notificação para Log de Alarme ID {id_log_alarme}: {e}", exc_info=True)
    finally:
        if conn_local:
            devolver_conexao(conn_local)

def notificar_dashboard_visual(id_log_alarme):
    # TODO: Implementar a lógica de notificação em tempo real (WebSocket).
    # Por enquanto, esta função não fará nada, pois a notificação visual
    # será feita pelo método de polling que vamos configurar a seguir.
    logger.info(f"Placeholder: A função de notificação via WebSocket para o alarme ID {id_log_alarme} foi chamada.")
    pass   

# Em planner_app.py, substitua esta função

@app.route('/api/verificar-novos-alarmes')
@login_requerido
def verificar_novos_alarmes():
    # Pega o ID do último alarme que o cliente já viu, enviado como parâmetro
    ultimo_id_visto = request.args.get('ultimo_id', 0, type=int)
    
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # --- INÍCIO DA CORREÇÃO ---
        # A consulta foi reescrita para ser sintaticamente válida.
        # Em vez de um LEFT JOIN inválido, usamos uma subconsulta no SELECT
        # para buscar o nome da máquina mais recente associada ao motivo de parada.
        query_corrigida = """
            SELECT TOP 5
                L.IDLogAlarme,
                L.DataHoraOcorrencia,
                M.Nome AS NomeMotivo,
                M.TipoAlarme,
                (SELECT TOP 1 R.NomeMaquina 
                 FROM TBL_StatusMaquina SM 
                 JOIN TBL_Recurso R ON SM.IDMaquina = R.IDMaquina
                 WHERE SM.IDMotivoParada = L.IDMotivoParadaGatilho 
                 ORDER BY SM.DataHoraInicio DESC) AS NomeMaquina
            FROM TBL_LogAlarmes L
            JOIN TBL_MotivoAlarme M ON L.IDMotivoAlarme = M.IDMotivoAlarme
            WHERE L.IDLogAlarme > ?
            ORDER BY L.IDLogAlarme ASC
        """
        cursor_local.execute(query_corrigida, (ultimo_id_visto,))
        # --- FIM DA CORREÇÃO ---
        
        alarmes = [dict(zip([column[0] for column in cursor_local.description], row)) for row in cursor_local.fetchall()]
        
        return jsonify(alarmes)
        
    except Exception as e:
        logger.error(f"Erro em /api/verificar-novos-alarmes: {e}", exc_info=True)
        return jsonify([]), 500 # Retorna lista vazia em caso de erro
    finally:
        if conn_local:
            devolver_conexao(conn_local)    

def disparar_alerta_estoque_baixo(cursor_local, id_materia_prima, nome_materia_prima, saldo_atual, limite_alerta, id_motivo_alarme_estoque):
    """
    Busca os destinatários e chama a função de envio de e-mail em uma nova thread.
    """
    try:
        # Busca os destinatários que assinam este motivo de alarme específico
        cursor_local.execute("""
            SELECT U.Email
            FROM TBL_AlarmeGrupoUsuario AGU
            JOIN TBL_GrupoUsuario GU ON AGU.IDGrupo = GU.IDGrupo
            JOIN TBL_Usuario U ON GU.IDGrupo = U.IDGrupo
            WHERE AGU.IDMotivoAlarme = ? AND U.Ativo = 1
        """, (id_motivo_alarme_estoque,))
        
        destinatarios_db = cursor_local.fetchall()
        destinatarios_emails = [row.Email for row in destinatarios_db]
        
        if not destinatarios_emails:
            logger.warning(f"Alerta de estoque baixo para {nome_materia_prima}, mas não há destinatários configurados para o ID do alarme {id_motivo_alarme_estoque}.")
            return

        assunto = f"ALERTA DE ESTOQUE BAIXO: {nome_materia_prima}"
        corpo = f"O estoque da matéria-prima '{nome_materia_prima}' atingiu um nível crítico.\n"
        corpo += f"Saldo atual: {saldo_atual:.2f} unidades.\n"
        corpo += f"Nível de alerta: {limite_alerta:.2f} unidades."

        # --- AQUI VOCÊ CHAMA A SUA FUNÇÃO DE ENVIO DE E-MAIL EXISTENTE ---
        # Substitua 'sua_funcao_de_envio_de_email_existente' pelo nome real da sua função
        # E ajuste os parâmetros para o que a sua função aceita
        # Por exemplo:
        # sua_funcao_de_envio_de_email_existente(destinatarios_emails, assunto, corpo)
        #
        # Por enquanto, vamos usar um placeholder para que o código compile.
        
        # O envio deve ser feito em uma thread para não bloquear a aplicação principal
        threading.Thread(target=sua_funcao_de_envio_de_email_existente, args=(destinatarios_emails, assunto, corpo)).start()
        
    except Exception as e:
        logger.error(f"Falha CRÍTICA ao disparar alerta de estoque baixo: {e}", exc_info=True)
        
# Em planner_app.py, SUBSTITUA a função da linha 6378:

@app.route('/relatorio_status', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relatorio_status')
def relatorio_status():
    conn_local = None
    resultados = []
    dados_gantt_json = '{}'
    dados_donut_json = '{}'

    hoje = datetime.now().strftime('%Y-%m-%d')
    filtros = {
        "data_inicio": request.form.get("data_inicio", hoje),
        "data_fim": request.form.get("data_fim", hoje),
        "id_maquina": request.form.get("id_maquina"),
        "id_turno": request.form.get("id_turno")
    }

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina")
        maquinas = cursor_local.fetchall()
        cursor_local.execute("SELECT IDTurno, NomeTurno FROM TBL_Turno WHERE Ativo = 1 ORDER BY NomeTurno")
        turnos = cursor_local.fetchall()

        if request.method == 'POST' and filtros["id_maquina"]:

            # +++++ INÍCIO DA ALTERAÇÃO (LÓGICA DE DATA DE REFERÊNCIA) +++++
            
            # 1. CTE para calcular a Data de Referência do Turno para cada status
            query = """
                WITH StatusComDataTurno AS (
                    SELECT 
                        SM.*,
                        T.IniciaDiaAnterior, T.HoraInicio AS HoraInicioTurno,
                        CASE
                            WHEN T.IniciaDiaAnterior = 1 AND CAST(SM.DataHoraInicio AS TIME) < CAST(T.HoraInicio AS TIME)
                            THEN CAST(DATEADD(day, -1, SM.DataHoraInicio) AS DATE)
                            ELSE CAST(SM.DataHoraInicio AS DATE)
                        END AS DataReferenciaTurno
                    FROM TBL_StatusMaquina SM
                    LEFT JOIN TBL_Turno T ON SM.IDTurno = T.IDTurno
                )
            -- 2. Query principal agora filtra pela DataReferenciaTurno
            SELECT
                SCDT.DataHoraInicio,
                ISNULL(SCDT.DataHoraFim, GETDATE()) AS DataHoraFim,
                DATEDIFF(SECOND, SCDT.DataHoraInicio, ISNULL(SCDT.DataHoraFim, GETDATE())) AS DuracaoSegundos,
                COALESCE(MP.Descricao, TS.NomeStatus, 'N/A') AS MotivoOuStatus,
                TS.NomeStatus AS CategoriaStatus,
                SCDT.ObsEvento,
                ExecInfo.CodigoOrdem, ExecInfo.NomeProduto
            FROM StatusComDataTurno SCDT
            JOIN TBL_TipoStatus TS ON SCDT.Status = TS.Status
            LEFT JOIN TBL_MotivoParada MP ON SCDT.IDMotivoParada = MP.IDMotivoParada
            OUTER APPLY (
                SELECT TOP 1 OP.CodigoOrdem, P.NomeProduto
                FROM TBL_ExecucaoOP EX
                JOIN TBL_OrdemProducao OP ON EX.IDOrdem = OP.IDOrdem
                JOIN TBL_Produto P ON OP.IDProduto = P.IDProduto
                WHERE EX.IDMaquina = SCDT.IDMaquina AND SCDT.DataHoraInicio >= EX.DataHoraInicio AND (SCDT.DataHoraInicio < EX.DataHoraFim OR EX.DataHoraFim IS NULL)
                ORDER BY EX.DataHoraInicio DESC
            ) AS ExecInfo
            WHERE 
              SCDT.IDMaquina = ?
              AND ISNULL(SCDT.IDMotivoParada, -1) <> ?
            """
            
            try:
                 # Converte as datas do filtro
                 data_inicio_dt = datetime.strptime(filtros["data_inicio"], "%Y-%m-%d")
                 data_fim_dt = datetime.strptime(filtros["data_fim"], "%Y-%m-%d")
            except ValueError:
                 flash("Formato de data inválido.", "error")
                 return render_template("relatorio_status.html",
                                        resultados=resultados, filtros=filtros,
                                        maquinas=maquinas, turnos=turnos,
                                        dados_gantt_json=dados_gantt_json,
                                        dados_donut_json=dados_donut_json)

            # 3. Adiciona os filtros de data e máquina
            # Filtra pela DataReferenciaTurno
            query += " AND SCDT.DataReferenciaTurno >= ? AND SCDT.DataReferenciaTurno <= ?"
            params = [int(filtros["id_maquina"]), ID_MOTIVO_FORA_DE_TURNO, data_inicio_dt, data_fim_dt]
            
            # +++++ FIM DA ALTERAÇÃO (LÓGICA DE DATA DE REFERÊNCIA) +++++

            if filtros["id_turno"]:
                query += " AND SCDT.IDTurno = ?"
                params.append(int(filtros["id_turno"]))

            query += " ORDER BY SCDT.DataHoraInicio ASC"

            logger.debug(f"Executando query relatorio_status (com DataReferenciaTurno): {query} com params: {params}")

            cursor_local.execute(query, params)
            resultados_raw = [dict(zip([column[0] for column in cursor_local.description], row)) for row in cursor_local.fetchall()]

            resultados = []
            tempo_por_status_seg = defaultdict(float)
            
            # Define o fim do dia do FILTRO (para o gráfico)
            data_fim_filtro_dt = data_fim_dt.replace(hour=23, minute=59, second=59)
            
            for r in resultados_raw:
                # Calcula a duração correta, limitando ao fim do dia filtrado se o evento ainda estiver ativo
                fim_real = r['DataHoraFim']
                
                # Esta lógica limita a barra se ela ainda estiver "Em andamento"
                if fim_real > data_fim_filtro_dt: 
                    # Se o evento ainda está ativo (DataHoraFim é GETDATE()) e já passou do dia filtrado
                    if r['DataHoraInicio'] < data_fim_filtro_dt:
                         fim_real = data_fim_filtro_dt # Limita a duração até o fim do dia do filtro
                    # Se o evento começou DEPOIS do dia do filtro (ex: turno da noite seguinte), mantém o fim real
                
                duracao_seg_recalculada = (fim_real - r['DataHoraInicio']).total_seconds()
                if duracao_seg_recalculada < 0: duracao_seg_recalculada = 0

                r['DuracaoSegundos'] = duracao_seg_recalculada
                r['DuracaoFormatada'] = formatar_segundos_para_hms(r['DuracaoSegundos'])
                tempo_por_status_seg[r['CategoriaStatus']] += r['DuracaoSegundos']
                resultados.append(r)

            if resultados:
                dados_donut = {
                    'labels': list(tempo_por_status_seg.keys()),
                    'data_minutos': [round(v / 60.0, 2) for v in tempo_por_status_seg.values()]
                }
                dados_donut_json = json.dumps(dados_donut, cls=DecimalEncoder)

                dados_gantt = {
                    'datasets': [{
                        'label': r['MotivoOuStatus'],
                        'data': [(r['DataHoraInicio'].isoformat(), min(r['DataHoraFim'], datetime.now()).isoformat())], # Usa o Fim real ou 'agora'
                        'backgroundColor': 'rgba(46, 125, 50, 0.7)' if r['CategoriaStatus'] == 'Produzindo' else 'rgba(211, 47, 47, 0.7)'
                    } for r in resultados]
                }
                dados_gantt_json = json.dumps(dados_gantt, cls=DecimalEncoder, default=str)


        return render_template("relatorio_status.html",
                               resultados=resultados,
                               filtros=filtros,
                               maquinas=maquinas,
                               turnos=turnos,
                               dados_gantt_json=dados_gantt_json,
                               dados_donut_json=dados_donut_json)

    except pyodbc.ProgrammingError as pe: 
        logger.error(f"Erro de Programação SQL em relatorio_status: {pe}", exc_info=True)
        try: logger.error(f"Query com erro: {query}")
        except NameError: logger.error("Variável 'query' não definida no momento do erro.")
        flash(f"Erro de sintaxe SQL ao gerar o relatório. Verifique os logs.", "error")
        return render_template("relatorio_status.html",
                               resultados=[], filtros=filtros, maquinas=maquinas, turnos=turnos,
                               dados_gantt_json='{}', dados_donut_json='{}')
    except Exception as e:
        logger.error(f"Erro em relatorio_status: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerar o relatório de status.", "error")
        return redirect(url_for('home')) 
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/relatorio_oee', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relatorio_oee')
def relatorio_oee():
    conn_local = None
    resultados_tabela = []
    dados_grafico_json = '{}'
    chart_title = 'Comparativo de OEE' # Título padrão
    maquinas = []
    turnos = []

    # --- Filtros (Incluindo codigo_ordem) ---
    filtros = {
        "data_inicio": request.form.get("data_inicio", datetime.now().strftime('%Y-%m-%d')) if request.method == 'POST' else request.args.get("data_inicio", datetime.now().strftime('%Y-%m-%d')),
        "data_fim": request.form.get("data_fim", datetime.now().strftime('%Y-%m-%d')) if request.method == 'POST' else request.args.get("data_fim", datetime.now().strftime('%Y-%m-%d')),
        "id_maquina": request.form.get("id_maquina", "") if request.method == 'POST' else request.args.get("id_maquina", ""),
        "id_turno": request.form.get("id_turno", "") if request.method == 'POST' else request.args.get("id_turno", ""),
        "codigo_ordem": request.form.get("codigo_ordem", "") if request.method == 'POST' else request.args.get("codigo_ordem", "") # NOVO FILTRO
    }

    try:
        conn_local = obter_conexao() # Use sua função de obter conexão
        cursor_local = conn_local.cursor()

        # Busca dados para os dropdowns de filtro (sempre)
        cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina")
        maquinas = cursor_local.fetchall()
        cursor_local.execute("SELECT IDTurno, NomeTurno FROM TBL_Turno WHERE Ativo = 1 ORDER BY NomeTurno")
        turnos = cursor_local.fetchall()

        # Executa a query principal apenas se for POST (submissão do formulário)
        if request.method == 'POST':
            logger.info(f"Gerando relatório OEE com filtros: {filtros}") # Log para debug

            # --- Query SQL ATUALIZADA (v3) com DataReferenciaTurno e partição por Ordem ---
            query = """
                WITH OEE_Com_DataTurno AS ( -- Calcula DataReferenciaTurno primeiro
                    SELECT
                        oee.*, -- Pega todas as colunas de TBL_IndiceOEE
                        t.NomeTurno,
                        t.IniciaDiaAnterior,
                        t.HoraInicio AS HoraInicioTurno,
                        -- Calcula a Data de Referência do Turno BASEADO NO MOMENTO DO CÁLCULO DO OEE
                        CASE
                            WHEN t.IniciaDiaAnterior = 1 AND CAST(oee.DataHoraCalculo AS TIME) < CAST(t.HoraInicio AS TIME)
                            THEN CAST(DATEADD(day, -1, oee.DataHoraCalculo) AS DATE) -- Atribui ao dia anterior
                            ELSE CAST(oee.DataHoraCalculo AS DATE) -- Usa a data do calendário do cálculo
                        END AS DataReferenciaTurno
                    FROM TBL_IndiceOEE AS oee WITH (NOLOCK)
                    -- JOIN com TBL_Turno aqui para ter a flag IniciaDiaAnterior
                    LEFT JOIN TBL_Turno t WITH (NOLOCK) ON oee.IDTurno = t.IDTurno
                ),
                OEE_Filtrado AS ( -- Aplica os filtros sobre os dados com DataReferenciaTurno
                    SELECT
                        oee_dt.Disponibilidade, oee_dt.Performance, oee_dt.Qualidade, oee_dt.OEE,
                        r.NomeMaquina,
                        oee_dt.DataReferenciaTurno, -- Usa a data calculada
                        oee_dt.IDTurno,
                        oee_dt.NomeTurno,
                        op.CodigoOrdem,
                        oee_dt.IDOrdem,
                        oee_dt.DataHoraCalculo -- Mantem DataHoraCalculo para ordenação do ROW_NUMBER
                    FROM OEE_Com_DataTurno AS oee_dt
                    JOIN TBL_Recurso r WITH (NOLOCK) ON oee_dt.IDMaquina = r.IDMaquina
                    LEFT JOIN TBL_OrdemProducao op WITH (NOLOCK) ON oee_dt.IDOrdem = op.IDOrdem
                    WHERE 1=1
                      -- Filtros (data_inicio, data_fim, id_maquina, id_turno, codigo_ordem)
                      -- serão adicionados aqui pela lógica Python, comparando com oee_dt.DataReferenciaTurno
            """
            params = []

            # Adiciona filtros de data (obrigatórios ou com padrão)
            try:
                # Usa as strings diretamente, pois a query compara com DATE
                if filtros["data_inicio"]:
                    query += " AND oee_dt.DataReferenciaTurno >= ?"
                    params.append(filtros["data_inicio"])
                if filtros["data_fim"]:
                     query += " AND oee_dt.DataReferenciaTurno <= ?"
                     params.append(filtros["data_fim"])
            except ValueError:
                 flash("Formato de data inválido.", "error")
                 # Retorna para a página com os filtros atuais e mensagem de erro
                 return render_template("relatorio_oee.html",
                                        resultados=resultados_tabela, filtros=filtros,
                                        maquinas=maquinas, turnos=turnos,
                                        dados_grafico_json=dados_grafico_json, chart_title=chart_title)


            # Adiciona filtros opcionais
            if filtros["id_maquina"]:
                query += " AND oee_dt.IDMaquina = ?"
                params.append(int(filtros["id_maquina"]))
            if filtros["id_turno"]:
                query += " AND oee_dt.IDTurno = ?"
                params.append(int(filtros["id_turno"]))
            if filtros["codigo_ordem"]:
                # Usamos LIKE para permitir busca parcial, ajuste para '=' se precisar de busca exata
                query += " AND op.CodigoOrdem LIKE ?"
                params.append(f"%{filtros['codigo_ordem']}%")

            query += """
                ),
                UltimoOEE_Por_Ordem_Grupo AS ( -- Aplica ROW_NUMBER usando DataReferenciaTurno
                    SELECT
                        *,
                        ROW_NUMBER() OVER(
                            -- <<< ALTERAÇÃO AQUI: Usa DataReferenciaTurno na partição e IDOrdem >>>
                            PARTITION BY NomeMaquina, DataReferenciaTurno, IDTurno, IDOrdem
                            ORDER BY DataHoraCalculo DESC -- Pega o mais recente DENTRO de cada ordem/grupo/data_ref
                        ) as rn
                    FROM OEE_Filtrado
                )
                SELECT
                    DataReferenciaTurno AS Data, -- Renomeia para compatibilidade
                    NomeMaquina, CodigoOrdem,
                    ISNULL(NomeTurno, 'Turno N/A') AS NomeTurno,
                    Disponibilidade * 100 AS Disponibilidade,
                    Performance * 100 AS Performance,
                    Qualidade * 100 AS Qualidade,
                    OEE * 100 AS OEE,
                    IDTurno -- Mantido para ordenação final
                FROM UltimoOEE_Por_Ordem_Grupo
                WHERE rn = 1
                ORDER BY DataReferenciaTurno, NomeMaquina, IDTurno, CodigoOrdem; -- Ordena pela data correta
            """
            # --- FIM DA QUERY ATUALIZADA ---

            logger.debug(f"Executando query OEE (v3 - DataTurno): {query} com params: {params}") # Log da query
            cursor_local.execute(query, params)
            # Fetchall e converte para dicionário ANTES de passar para o template
            resultados_raw = cursor_local.fetchall()
            resultados_tabela = [dict(zip([column[0] for column in cursor_local.description], row)) for row in resultados_raw]
            logger.info(f"Query OEE (v3 - DataTurno) retornou {len(resultados_tabela)} resultados.") # Log do resultado

            # --- Lógica AJUSTADA para Geração dos Rótulos do Gráfico e Título ---
            if resultados_tabela:
                if filtros["codigo_ordem"]:
                    chart_title = f"Último OEE para Ordem {filtros['codigo_ordem']}"
                    labels_grafico = [f"{r['Data'].strftime('%d/%m')} - {r['NomeMaquina']} - {r['NomeTurno']}" for r in resultados_tabela]
                elif not filtros["id_maquina"] and not filtros["id_turno"]:
                    chart_title = "Último OEE por Ordem / Máquina / Turno"
                    labels_grafico = [f"{r['Data'].strftime('%d/%m')}-{r['NomeMaquina']}-{r['NomeTurno']}-{r.get('CodigoOrdem','N/A')}" for r in resultados_tabela]
                elif filtros["id_maquina"] and not filtros["id_turno"]:
                    maquina_sel = next((m.NomeMaquina for m in maquinas if str(m.IDMaquina) == filtros["id_maquina"]), "")
                    chart_title = f"Último OEE por Ordem/Turno - {maquina_sel}"
                    labels_grafico = [f"{r['Data'].strftime('%d/%m')}-{r['NomeTurno']}-{r.get('CodigoOrdem','N/A')}" for r in resultados_tabela]
                elif not filtros["id_maquina"] and filtros["id_turno"]:
                    turno_sel = next((t.NomeTurno for t in turnos if str(t.IDTurno) == filtros["id_turno"]), "")
                    chart_title = f"Último OEE por Ordem/Máquina - {turno_sel}"
                    labels_grafico = [f"{r['Data'].strftime('%d/%m')}-{r['NomeMaquina']}-{r.get('CodigoOrdem','N/A')}" for r in resultados_tabela]
                else: # Filtrou máquina E turno
                    maquina_sel = next((m.NomeMaquina for m in maquinas if str(m.IDMaquina) == filtros["id_maquina"]), "")
                    turno_sel = next((t.NomeTurno for t in turnos if str(t.IDTurno) == filtros["id_turno"]), "")
                    chart_title = f"Último OEE por Ordem - {maquina_sel} - {turno_sel}"
                    labels_grafico = [f"{r['Data'].strftime('%d/%m')}-{r.get('CodigoOrdem','N/A')}" for r in resultados_tabela]

                # Montagem dos datasets para o gráfico (sem alteração na estrutura)
                dados_oee = [r['OEE'] for r in resultados_tabela]
                dados_disponibilidade = [r['Disponibilidade'] for r in resultados_tabela]
                dados_performance = [r['Performance'] for r in resultados_tabela]
                dados_qualidade = [r['Qualidade'] for r in resultados_tabela]

                datasets_grafico = [
                    {'label': 'OEE (%)', 'data': dados_oee, 'backgroundColor': 'rgb(75, 192, 192)'},
                    {'label': 'Disponibilidade (%)', 'data': dados_disponibilidade, 'backgroundColor': 'rgb(255, 159, 64)'},
                    {'label': 'Performance (%)', 'data': dados_performance, 'backgroundColor': 'rgb(255, 99, 132)'},
                    {'label': 'Qualidade (%)', 'data': dados_qualidade, 'backgroundColor': 'rgb(54, 162, 235)'}
                ]

                # Usa o DecimalEncoder para serializar corretamente
                # Passa default=str para tratar datas que o DecimalEncoder não pega
                dados_grafico_json = json.dumps({'labels': labels_grafico, 'datasets': datasets_grafico}, cls=DecimalEncoder, default=str)
                logger.debug(f"JSON do gráfico gerado (v3 DataTurno): {dados_grafico_json[:200]}...") # Log do JSON (parcial)
            else:
                logger.info("Nenhum dado encontrado para os filtros selecionados (v3 DataTurno).")
                flash("Nenhum dado encontrado para o período e filtros selecionados.", "info")

        # Renderiza o template passando todos os dados necessários
        # resultados_tabela agora é uma lista de dicionários
        return render_template("relatorio_oee.html",
                               resultados=resultados_tabela,
                               filtros=filtros,
                               maquinas=maquinas,
                               turnos=turnos,
                               dados_grafico_json=dados_grafico_json,
                               chart_title=chart_title) # Passa o título dinâmico

    except Exception as e:
        logger.error(f"Erro CRÍTICO em relatorio_oee (v3 DataTurno): {e}", exc_info=True)
        flash("Ocorreu um erro inesperado ao gerar o relatório de OEE.", "error")
        # Em caso de erro, renderiza a página com dados vazios mas mantém os filtros e dropdowns
        return render_template("relatorio_oee.html",
                               resultados=[], filtros=filtros,
                               maquinas=maquinas, turnos=turnos,
                               dados_grafico_json='{}', chart_title='Erro ao Gerar Relatório')
    finally:
        if conn_local:
            devolver_conexao(conn_local) # Use sua função de devolver conexão
            
# Em planner_app.py, substitua a função exportar_relatorio_oee

@app.route('/relatorio_oee/exportar', methods=['POST'])
@login_requerido
@permissao_requerida('/relatorio_oee')
def exportar_relatorio_oee():
    conn_local = None
    try:
        data = request.json
        export_type = data.get('exportType', 'ambos')
        filtros = {
            "data_inicio": data.get("data_inicio"), "data_fim": data.get("data_fim"),
            "id_maquina": data.get("id_maquina"), "id_turno": data.get("id_turno"),
            "codigo_ordem": data.get("codigo_ordem") # <<< RECEBE O FILTRO DE ORDEM
        }
        logger.info(f"Iniciando exportação OEE (Tipo: {export_type}) com filtros: {filtros}")

        conn_local = obter_conexao()
        # cursor_local = conn_local.cursor() # Não é mais necessário com read_sql

        # --- USA EXATAMENTE A MESMA QUERY DA ROTA PRINCIPAL (relatorio_oee) ---
        query = """
            WITH OEE_Filtrado AS (
                SELECT oee.*, r.NomeMaquina, CAST(oee.DataHoraCalculo AS DATE) as Data,
                       t.NomeTurno, op.CodigoOrdem, oee.DataHoraCalculo as TimestampCalculo
                FROM TBL_IndiceOEE AS oee
                JOIN TBL_Recurso r ON oee.IDMaquina = r.IDMaquina
                LEFT JOIN TBL_Turno t ON oee.IDTurno = t.IDTurno
                LEFT JOIN TBL_OrdemProducao op ON oee.IDOrdem = op.IDOrdem
                WHERE 1=1
        """
        params = []
        if filtros["data_inicio"]:
            query += " AND CAST(oee.DataHoraCalculo AS DATE) >= ?"
            params.append(filtros["data_inicio"])
        if filtros["data_fim"]:
            query += " AND CAST(oee.DataHoraCalculo AS DATE) <= ?"
            params.append(filtros["data_fim"])
        if filtros["id_maquina"]:
            query += " AND oee.IDMaquina = ?"
            params.append(int(filtros["id_maquina"]))
        if filtros["id_turno"]:
            query += " AND oee.IDTurno = ?"
            params.append(int(filtros["id_turno"]))
        if filtros["codigo_ordem"]:
            query += " AND op.CodigoOrdem LIKE ?" # << FILTRO DE ORDEM
            params.append(f"%{filtros['codigo_ordem']}%")

        query += """
            ), UltimoOEE_PorGrupo AS (
                SELECT *, ROW_NUMBER() OVER(PARTITION BY NomeMaquina, Data, IDTurno ORDER BY TimestampCalculo DESC) as rn
                FROM OEE_Filtrado
            )
            SELECT
                Data, NomeMaquina, CodigoOrdem, -- << Adicionado CodigoOrdem
                ISNULL(NomeTurno, 'Turno N/A') AS NomeTurno,
                Disponibilidade * 100 AS Disponibilidade, Performance * 100 AS Performance,
                Qualidade * 100 AS Qualidade, OEE * 100 AS OEE
                -- Removido IDTurno do select final, desnecessário para o Excel
            FROM UltimoOEE_PorGrupo WHERE rn = 1
            ORDER BY Data, NomeMaquina, IDTurno; -- Mantém a ordenação lógica
        """
        # --- FIM DA QUERY ---

        df = pd.DataFrame() # Inicializa vazio
        if export_type in ['tabela', 'ambos']:
            logger.debug("Executando query para dados da tabela de exportação OEE (com filtro OP)...")
            df = pd.read_sql(query, conn_local, params=params)
            logger.info(f"Consulta para exportação OEE (com filtro OP) retornou {len(df)} linhas.")

            if not df.empty:
                 df['Data'] = pd.to_datetime(df['Data']).dt.strftime('%d/%m/%Y')
                 df.rename(columns={
                     'Data': 'Data', 'NomeMaquina': 'Máquina', 'CodigoOrdem': 'Ordem', # << Renomeado
                     'NomeTurno': 'Turno', 'Disponibilidade': 'Disponibilidade (%)',
                     'Performance': 'Performance (%)', 'Qualidade': 'Qualidade (%)', 'OEE': 'OEE (%)'
                 }, inplace=True)
                 # << Adicionado 'Ordem' à lista de colunas
                 df = df[['Data', 'Máquina', 'Ordem', 'Turno', 'Disponibilidade (%)', 'Performance (%)', 'Qualidade (%)', 'OEE (%)']]
            else:
                 logger.warning("Nenhum dado encontrado para a tabela de exportação OEE (com filtro OP).")

        # Geração do arquivo Excel (lógica existente)
        # ... (código para gerar Excel com openpyxl, adicionar gráfico se necessário) ...
        output = io.BytesIO()
        with pd.ExcelWriter(output, engine='openpyxl') as writer:
            df.to_excel(writer, index=False, sheet_name='OEE Detalhado')
            worksheet = writer.sheets['OEE Detalhado']

            if export_type in ['grafico', 'ambos'] and 'chartImage' in data and data['chartImage']:
                try:
                    logger.info("Adicionando gráfico OEE (com filtro OP) ao arquivo Excel...")
                    # ... (código para decodificar e adicionar imagem) ...
                    base64_image_data = data['chartImage'].split(',')[1]
                    image_data = base64.b64decode(base64_image_data)
                    img = Image(io.BytesIO(image_data))
                    img.anchor = 'A' + str(len(df) + 3)
                    worksheet.add_image(img)
                    logger.info("Gráfico OEE (com filtro OP) adicionado com sucesso.")
                except Exception as img_err:
                     logger.error(f"Erro ao adicionar imagem do gráfico OEE (com filtro OP) ao Excel: {img_err}", exc_info=True)

        output.seek(0)
        logger.info("Arquivo Excel OEE (com filtro OP) gerado. Enviando para download...")
        return send_file(...) # Sua função send_file existente

    except Exception as e:
        logger.error(f"Erro CRÍTICO ao exportar relatório de OEE (com filtro OP): {e}", exc_info=True)
        return jsonify({"error": f"Falha ao gerar o arquivo Excel: {str(e)}"}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)   
            
@app.route('/relatorio_paradas', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relatorio_paradas')
def relatorio_paradas():
    conn_local = None
    agrupado_por_maquina = []
    dados_pareto = {}
    kpis = {
        'total_parado_formatado': "00:00:00",
        'ocorrencias': 0,
        'mtbf_formatado': "00:00:00",
        'mttr_formatado': "00:00:00"
    }

    filtros = {
        'data_inicio': request.form.get('data_inicio', (datetime.now() - timedelta(days=7)).strftime('%Y-%m-%d')),
        'data_fim': request.form.get('data_fim', datetime.now().strftime('%Y-%m-%d')),
        'id_maquina': request.form.get('id_maquina'),
        'id_turno': request.form.get('id_turno') 
    }

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina")
        maquinas = cursor_local.fetchall()
        cursor_local.execute("SELECT IDTurno, NomeTurno FROM TBL_Turno WHERE Ativo = 1 ORDER BY NomeTurno")
        turnos = cursor_local.fetchall()

        if request.method == 'POST':
            # 1. Parseia as datas do filtro
            data_inicio_dt = datetime.strptime(filtros['data_inicio'], '%Y-%m-%d')
            data_fim_dt = datetime.strptime(filtros['data_fim'], '%Y-%m-%d')

            # 2. Define o CTE base
            base_cte = """
                WITH StatusComDataTurno AS (
                    SELECT 
                        SM.IDMaquina, SM.IDTurno, SM.DataHoraInicio, SM.DataHoraFim, 
                        SM.IDMotivoParada, SM.Status, SM.ObsEvento, -- Incluído ObsEvento aqui
                        T.IniciaDiaAnterior, T.HoraInicio AS HoraInicioTurno,
                        CASE
                            WHEN T.IniciaDiaAnterior = 1 AND CAST(SM.DataHoraInicio AS TIME) < CAST(T.HoraInicio AS TIME)
                            THEN CAST(DATEADD(day, -1, SM.DataHoraInicio) AS DATE)
                            ELSE CAST(SM.DataHoraInicio AS DATE)
                        END AS DataReferenciaTurno
                    FROM TBL_StatusMaquina SM
                    LEFT JOIN TBL_Turno T ON SM.IDTurno = T.IDTurno
                )
            """
            
            # 3. Define o WHERE clause
            cte_where_clause = " WHERE SCDT.DataReferenciaTurno BETWEEN ? AND ? AND SCDT.Status = 0 AND SCDT.IDMotivoParada <> ?"
            params = [data_inicio_dt, data_fim_dt, ID_MOTIVO_FORA_DE_TURNO]

            if filtros['id_maquina']:
                cte_where_clause += " AND SCDT.IDMaquina = ?"
                params.append(int(filtros['id_maquina']))
            if filtros['id_turno']:
                cte_where_clause += " AND SCDT.IDTurno = ?"
                params.append(int(filtros['id_turno']))
            
            # 4. Query de Detalhes (COM A COLUNA ObsEvento)
            query_detalhes = base_cte + f"""
                SELECT R.NomeMaquina, SCDT.DataHoraInicio, SCDT.DataHoraFim,
                       DATEDIFF(SECOND, SCDT.DataHoraInicio, ISNULL(SCDT.DataHoraFim, GETDATE())) AS DuracaoSegundos,
                       ISNULL(MP.Descricao, 'Não Classificada') AS MotivoParada,
                       SCDT.ObsEvento -- << CAMPO IMPORTANTE ADICIONADO
                FROM StatusComDataTurno SCDT
                JOIN TBL_Recurso R ON SCDT.IDMaquina = R.IDMaquina
                LEFT JOIN TBL_MotivoParada MP ON SCDT.IDMotivoParada = MP.IDMotivoParada
                {cte_where_clause} ORDER BY R.NomeMaquina, SCDT.DataHoraInicio
            """
            cursor_local.execute(query_detalhes, params)
            
            detalhes_raw = [dict(zip([column[0] for column in cursor_local.description], row)) for row in cursor_local.fetchall()]
            temp_dict = defaultdict(lambda: {'maquina': '', 'total_segundos': 0, 'paradas': []})
            
            for parada in detalhes_raw:
                parada['DuracaoFormatada'] = formatar_segundos_para_hms(parada['DuracaoSegundos'])
                chave = parada['NomeMaquina']
                temp_dict[chave]['maquina'] = chave
                temp_dict[chave]['total_segundos'] += parada['DuracaoSegundos']
                temp_dict[chave]['paradas'].append(parada)
            
            for key in temp_dict:
                temp_dict[key]['total_formatado'] = formatar_segundos_para_hms(temp_dict[key]['total_segundos'])
            
            agrupado_por_maquina = list(temp_dict.values())

            # 5. Query do Pareto (mantida igual)
            query_pareto = base_cte + f"""
                SELECT
                    ISNULL(MP.Descricao, 'Não Classificada') as Motivo,
                    ISNULL(MP.FlgPlanejada, 0) as Planejada,
                    SUM(CAST(DATEDIFF(SECOND, SCDT.DataHoraInicio, ISNULL(SCDT.DataHoraFim, GETDATE())) AS FLOAT)) as DuracaoSegundos
                FROM StatusComDataTurno SCDT
                LEFT JOIN TBL_MotivoParada MP ON SCDT.IDMotivoParada = MP.IDMotivoParada
                {cte_where_clause}
                GROUP BY ISNULL(MP.Descricao, 'Não Classificada'), ISNULL(MP.FlgPlanejada, 0)
                HAVING SUM(CAST(DATEDIFF(SECOND, SCDT.DataHoraInicio, ISNULL(SCDT.DataHoraFim, GETDATE())) AS FLOAT)) > 0
                ORDER BY DuracaoSegundos DESC
            """
            cursor_local.execute(query_pareto, params)
            pareto_raw = cursor_local.fetchall()
            
            if pareto_raw:
                total_paradas_seg = sum(p.DuracaoSegundos for p in pareto_raw)
                labels = [p.Motivo for p in pareto_raw]
                data_bar_minutos = [round(p.DuracaoSegundos / 60.0, 2) for p in pareto_raw]
                cores_barras = ['rgba(46, 125, 50, 0.6)' if p.Planejada == 1 else 'rgba(211, 47, 47, 0.6)' for p in pareto_raw]
                flags_planejada = [p.Planejada for p in pareto_raw]
                acumulado = 0
                data_line = []
                for p in pareto_raw:
                    acumulado += p.DuracaoSegundos
                    data_line.append(round((acumulado / total_paradas_seg) * 100, 2) if total_paradas_seg > 0 else 0)
                dados_pareto = {
                    'labels': labels, 'data_bar_minutos': data_bar_minutos, 'data_line': data_line,
                    'colors': cores_barras, 'planejada_flags': flags_planejada
                }

            # 6. KPIs (mantidos iguais)
            kpi_where_clause = " WHERE SCDT_KPI.DataReferenciaTurno BETWEEN ? AND ?"
            kpi_params = [data_inicio_dt, data_fim_dt]
            if filtros['id_maquina']:
                kpi_where_clause += " AND SCDT_KPI.IDMaquina = ?"
                kpi_params.append(int(filtros['id_maquina']))
            if filtros['id_turno']:
                kpi_where_clause += " AND SCDT_KPI.IDTurno = ?"
                kpi_params.append(int(filtros['id_turno']))

            kpi_parada_filter = f" AND SCDT_KPI.IDMotivoParada <> {ID_MOTIVO_FORA_DE_TURNO}" 
            
            sql_kpis = base_cte.replace("StatusComDataTurno", "StatusComDataTurno_KPI") + f"""
                SELECT
                    (SELECT COUNT(*) FROM StatusComDataTurno_KPI SCDT_KPI {kpi_where_clause} AND Status = 0 {kpi_parada_filter}) as Ocorrencias,
                    (SELECT SUM(DATEDIFF(SECOND, DataHoraInicio, ISNULL(DataHoraFim, GETDATE()))) FROM StatusComDataTurno_KPI SCDT_KPI {kpi_where_clause} AND Status = 1) as TempoProduzindoSeg,
                    (SELECT SUM(DATEDIFF(SECOND, DataHoraInicio, ISNULL(DataHoraFim, GETDATE()))) FROM StatusComDataTurno_KPI SCDT_KPI {kpi_where_clause} AND Status = 0 {kpi_parada_filter}) as TempoParadoSeg
            """
            
            cursor_local.execute(sql_kpis, kpi_params * 3)
            kpi_data = cursor_local.fetchone()
            if kpi_data: 
                ocorrencias_kpi = kpi_data.Ocorrencias if kpi_data.Ocorrencias is not None else 0
                tempo_parado_kpi = kpi_data.TempoParadoSeg if kpi_data.TempoParadoSeg is not None else 0
                tempo_produzindo_kpi = kpi_data.TempoProduzindoSeg if kpi_data.TempoProduzindoSeg is not None else 0

                if ocorrencias_kpi > 0:
                    kpis['ocorrencias'] = ocorrencias_kpi
                    kpis['total_parado_formatado'] = formatar_segundos_para_hms(tempo_parado_kpi)
                    kpis['mttr_formatado'] = formatar_segundos_para_hms(tempo_parado_kpi / ocorrencias_kpi)
                    kpis['mtbf_formatado'] = formatar_segundos_para_hms(tempo_produzindo_kpi / ocorrencias_kpi)
                else:
                    kpis['ocorrencias'] = 0
                    kpis['total_parado_formatado'] = "00:00:00"
                    kpis['mttr_formatado'] = "00:00:00"
                    kpis['mtbf_formatado'] = "00:00:00"

        dados_pareto_json = json.dumps(dados_pareto, cls=DecimalEncoder)
        
        return render_template('relatorio_paradas.html',
                               agrupado=agrupado_por_maquina,
                               filtros=filtros, kpis=kpis,
                               dados_pareto_json=dados_pareto_json,
                               maquinas=maquinas,
                               turnos=turnos)
    except Exception as e:
        logger.error(f"Erro em relatorio_paradas: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerar o relatório de paradas.", "error")
        return render_template('relatorio_paradas.html',
                               agrupado=[], filtros=filtros, kpis=kpis,
                               dados_pareto_json='{}', maquinas=maquinas,
                               turnos=turnos)
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/api/paradas/detalhe_mensal')
@login_requerido
def detalhe_mensal_parada():
    conn_local = None
    try:
        motivo = request.args.get('motivo', type=str)
        id_maquina = request.args.get('id_maquina', default=None)

        if not motivo:
            return jsonify({"success": False, "message": "Motivo da parada não fornecido."}), 400

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        query = """
            SELECT
                MONTH(SM.DataHoraInicio) as Mes,
                SUM(DATEDIFF(SECOND, SM.DataHoraInicio, ISNULL(SM.DataHoraFim, GETDATE()))) as TotalSegundos
            FROM TBL_StatusMaquina SM
            LEFT JOIN TBL_MotivoParada MP ON SM.IDMotivoParada = MP.IDMotivoParada
            WHERE
                ISNULL(MP.Descricao, 'Não Classificada') = ?
                AND YEAR(SM.DataHoraInicio) = YEAR(GETDATE())
        """
        params = [motivo]

        if id_maquina and id_maquina.isdigit() and int(id_maquina) > 0:
            query += " AND SM.IDMaquina = ?"
            params.append(int(id_maquina))

        query += " GROUP BY MONTH(SM.DataHoraInicio) ORDER BY Mes ASC"

        cursor_local.execute(query, params)
        
        # ---> INÍCIO DA LÓGICA ATUALIZADA <---
        # Cria um dicionário com os resultados do banco
        resultados_db = {row.Mes: row.TotalSegundos for row in cursor_local.fetchall()}
        
        # Cria uma lista final para os 12 meses, preenchendo com 0 onde não houver dados
        dados_finais = []
        for mes_num in range(1, 13):
            dados_finais.append({
                "Mes": mes_num,
                "TotalSegundos": resultados_db.get(mes_num, 0)
            })
        # ---> FIM DA LÓGICA ATUALIZADA <---
        
        return jsonify({"success": True, "dados": dados_finais})

    except Exception as e:
        logger.error(f"Erro em detalhe_mensal_parada: {e}", exc_info=True)
        return jsonify({"success": False, "message": "Erro interno no servidor."}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)



# planner_app.py (adicione esta nova rota ao final do arquivo)

@app.route('/relatorio_estornos', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relatorio_estornos')
def relatorio_estornos():
    conn_local = None
    resultados = []
    
    filtros = {
        "data_inicio": request.form.get("data_inicio", (datetime.now() - timedelta(days=7)).strftime('%Y-%m-%d')),
        "data_fim": request.form.get("data_fim", datetime.now().strftime('%Y-%m-%d'))
    }

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            data_inicio_dt = datetime.strptime(filtros["data_inicio"], "%Y-%m-%d")
            data_fim_dt = datetime.strptime(filtros["data_fim"], "%Y-%m-%d").replace(hour=23, minute=59, second=59)

            # --- ALTERAÇÃO AQUI: Adicionada subquery para a Produção Líquida ---
            query = """
                SELECT 
                    E.DataHoraEvento,
                    R.NomeMaquina,
                    P.NomeProduto,
                    OP.CodigoOrdem,
                    OP.QuantidadePlanejada,
                    ISNULL((SELECT SUM(gross.Quantidade) 
                        FROM VW_EventoProducaoComCicloReal gross 
                        WHERE gross.IDOrdemProducao = E.IDOrdemProducao AND gross.TipoValor = 'BOA'
                    ), 0) AS QuantidadeProduzidaBruta,
                    ISNULL((SELECT SUM(net.Quantidade) 
                        FROM VW_EventoProducaoComCicloReal net 
                        WHERE net.IDOrdemProducao = E.IDOrdemProducao AND net.TipoValor IN ('BOA', 'ESTORNO')
                    ), 0) AS QuantidadeProduzidaLiquida,
                    ISNULL((SELECT SUM(scrap.Quantidade)
                        FROM VW_EventoProducaoComCicloReal scrap
                        WHERE scrap.IDOrdemProducao = E.IDOrdemProducao AND scrap.TipoValor = 'REFUGO'
                    ), 0) AS QuantidadeRefugadaTotal,
                    -E.Quantidade AS QuantidadeEstornada,
                    E.ObsEvento AS MotivoEstorno,
                    U.NomeUsuario AS NomeOperador
                FROM 
                    VW_EventoProducaoComCicloReal E
                JOIN TBL_OrdemProducao OP ON E.IDOrdemProducao = OP.IDOrdem
                JOIN TBL_Produto P ON OP.IDProduto = P.IDProduto
                JOIN TBL_Recurso R ON E.IDMaquina = R.IDMaquina
                LEFT JOIN TBL_Usuario U ON E.IDOperador = U.IDUsuario
                WHERE 
                    E.TipoValor = 'ESTORNO'
                    AND E.DataHoraEvento BETWEEN ? AND ?
                ORDER BY 
                    E.DataHoraEvento DESC
            """
            
            cursor_local.execute(query, (data_inicio_dt, data_fim_dt))
            resultados = [dict(zip([column[0] for column in cursor_local.description], row)) for row in cursor_local.fetchall()]

        return render_template("relatorio_estornos.html", 
                               resultados=resultados, 
                               filtros=filtros)
    except Exception as e:
        logger.error(f"Erro em relatorio_estornos: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerar o relatório de estornos.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
            
@app.route('/cadastro_grupo_alarme', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_grupo_alarme')
def cadastro_grupo_alarme():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_grupo = request.args.get('id')
        grupo_editar = None

        if request.method == 'POST':
            id_grupo_form = request.form.get('id_grupo')
            codigo = request.form['codigo']
            nome = request.form['nome']
            descricao = request.form['descricao']
            ativo = 1 if 'ativo' in request.form else 0

            if id_grupo_form:
                cursor_local.execute("""
                    UPDATE TBL_GrupoAlarme
                    SET Codigo = ?, Nome = ?, Descricao = ?, Ativo = ?, DataAtualizacao = GETDATE()
                    WHERE IDGrupoAlarme = ?
                """, (codigo, nome, descricao, ativo, id_grupo_form))
                flash("Grupo de alarme atualizado com sucesso!", "success")
            else:
                cursor_local.execute("""
                    INSERT INTO TBL_GrupoAlarme (Codigo, Nome, Descricao, Ativo, DataCriacao)
                    VALUES (?, ?, ?, ?, GETDATE())
                """, (codigo, nome, descricao, ativo))
                flash("Grupo de alarme cadastrado com sucesso!", "success")

            conn_local.commit()
            return redirect(url_for('cadastro_grupo_alarme'))

        if id_grupo:
            cursor_local.execute("SELECT * FROM TBL_GrupoAlarme WHERE IDGrupoAlarme = ?", (id_grupo,))
            grupo_editar = cursor_local.fetchone()

        cursor_local.execute("SELECT * FROM TBL_GrupoAlarme ORDER BY Nome")
        grupos = cursor_local.fetchall()

        return render_template('cadastro_grupo_alarme.html', grupos=grupos, grupo_editar=grupo_editar)
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em cadastro_grupo_alarme: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar grupos de alarme.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
    
@app.route('/alterar_status_grupo_alarme/<int:id_grupo>/<int:status>')
@login_requerido
@permissao_requerida('/cadastro_grupo_alarme')
def alterar_status_grupo_alarme(id_grupo, status):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("""
            UPDATE TBL_GrupoAlarme
            SET Ativo = ?, DataAtualizacao = GETDATE()
            WHERE IDGrupoAlarme = ?
        """, (status, id_grupo))
        conn_local.commit()
        flash("Status do grupo de alarme alterado!", "success")
        return redirect(url_for('cadastro_grupo_alarme'))
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em alterar_status_grupo_alarme: {e}", exc_info=True)
        flash("Ocorreu um erro ao alterar o status do grupo de alarme.", "error")
        return redirect(url_for('cadastro_grupo_alarme'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

def verificar_inatividade_maquinas():
    """
    SUPERVISOR DE INATIVIDADE (ROBÔ):
    Verifica se máquinas em produção pararam de enviar pulsos.
    
    ATUALIZAÇÃO CRÍTICA: Agora ele consulta a TBL_AgendaConsolidada antes de agir.
    Se for horário de Café/Almoço (Status Planejado = 0), ele NÃO toca na máquina,
    permitindo que o status de "Café" permaneça.
    """
    conn_thread = None
    try:
        conn_thread = conectar_bd()
        cursor_thread = conn_thread.cursor()

        # Busca máquinas ativas
        cursor_thread.execute("SELECT IDMaquina, LimiteInatividadeSegundos, Automatico FROM TBL_Recurso WHERE Ativo = 1")
        todas_maquinas_ativas = cursor_thread.fetchall()

        for maquina in todas_maquinas_ativas:
            id_maquina = maquina.IDMaquina
            
            # ==============================================================================
            # 1. TRAVA DE SEGURANÇA: CONSULTA A AGENDA ANTES DE AGIR
            # ==============================================================================
            try:
                agora = datetime.now()
                # Verifica o que a agenda manda fazer AGORA
                cursor_thread.execute("""
                    SELECT TOP 1 EstadoPlanejado 
                    FROM TBL_AgendaConsolidada 
                    WHERE IDMaquina = ? 
                      AND ? BETWEEN HoraInicio AND HoraFim
                """, (id_maquina, agora))
                
                agenda_atual = cursor_thread.fetchone()
                
                # SE a agenda diz que é para estar PARADO (Estado 0), o Supervisor de Inatividade NÃO MEXE.
                # Isso impede que ele sobrescreva "Café" com "Não Identificada".
                if agenda_atual and agenda_atual.EstadoPlanejado == 0:
                    continue 
            except Exception as e_agenda:
                logger.error(f"SUPERVISOR: Erro ao verificar agenda para maq {id_maquina}: {e_agenda}")
            # ==============================================================================

            try:
                # 2. Lógica Original de Verificação de Inatividade
                cursor_thread.execute("""
                    SELECT TOP 1 Status, IDMotivoParada, DataHoraInicio
                    FROM TBL_StatusMaquina
                    WHERE IDMaquina = ? AND DataHoraFim IS NULL
                    ORDER BY DataHoraRegistro DESC
                """, id_maquina)
                status_atual_row = cursor_thread.fetchone()
                status_atual = status_atual_row.Status if status_atual_row else -1

                id_turno_maquina_ativo = identificar_turno_da_maquina(conn_thread, cursor_thread, id_maquina)

                # Tratamento de Fora de Turno (Mantém igual)
                if id_turno_maquina_ativo is None:
                    if status_atual != 0 or (status_atual_row and status_atual_row.IDMotivoParada != ID_MOTIVO_FORA_DE_TURNO):
                        _update_machine_status(conn_thread, cursor_thread, id_maquina, 0, ID_MOTIVO_FORA_DE_TURNO, "Supervisor: Fora de Turno")
                    continue

                if status_atual == 0 and status_atual_row and status_atual_row.IDMotivoParada == ID_MOTIVO_FORA_DE_TURNO:
                    _update_machine_status(conn_thread, cursor_thread, id_maquina, 0, ID_MOTIVO_PARADA_AUTOMATICA, "Supervisor: Início de turno")
                    continue

                # 3. Verifica Inatividade (Apenas se a máquina deve estar RODANDO)
                if maquina.Automatico == 1:
                    # Só atua se o status atual NÃO for 0 (Parado).
                    # Se já está parado (e não foi pego pela trava da agenda acima), deixa como está.
                    if status_atual != 0: 
                        limite_da_maquina = maquina.LimiteInatividadeSegundos if maquina.LimiteInatividadeSegundos else 30
                        ponto_de_referencia = status_atual_row.DataHoraInicio if status_atual_row else datetime.now()

                        cursor_thread.execute("SELECT TOP 1 DataHoraEvento FROM VW_EventoProducaoComCicloReal WHERE IDMaquina = ? AND TipoValor='BOA' ORDER BY DataHoraEvento DESC", id_maquina)
                        ultimo_pulso_row = cursor_thread.fetchone()

                        if ultimo_pulso_row and ultimo_pulso_row.DataHoraEvento > ponto_de_referencia:
                            ponto_de_referencia = ultimo_pulso_row.DataHoraEvento

                        tempo_sem_atividade = (datetime.now() - ponto_de_referencia).total_seconds()

                        if tempo_sem_atividade > limite_da_maquina:
                            cursor_thread.execute("SELECT TOP 1 IDExecucao FROM TBL_ExecucaoOP WHERE IDMaquina = ? AND Status = 'Em Execucao'", (id_maquina,))
                            execucao_ativa = cursor_thread.fetchone()
                            obs_evento = "Parada automática por inatividade"
                            
                            data_inicio_retroativa = ponto_de_referencia + timedelta(seconds=1)
                            
                            _update_machine_status(
                                conn_thread, cursor_thread, 
                                id_maquina, 
                                0, # Derruba para Parada
                                ID_MOTIVO_PARADA_AUTOMATICA, # Motivo: Não Identificada
                                obs_evento,
                                data_hora_custom=data_inicio_retroativa
                            )

            except Exception as e:
                logger.error(f"SUPERVISOR: Erro ao processar máquina {id_maquina}: {e}", exc_info=True)

        conn_thread.commit()

    except Exception as e:
        logger.error(f"SUPERVISOR: Erro GERAL no ciclo: {str(e)}", exc_info=True)
        if conn_thread: conn_thread.rollback()
    finally:
        if conn_thread:
            try:
                conn_thread.close()
            except Exception:
                pass


def registrar_parada_por_inatividade(id_maquina, conn_thread, cursor_thread):
    """
    Função auxiliar que executa os comandos para registrar uma parada por inatividade.
    NÃO faz commit ou rollback. Apenas executa os comandos na transação existente.
    """
    try:
        # Chama a função _update_machine_status que já centraliza a lógica de mudar o status.
        # Passamos os objetos de conexão e cursor existentes.
        _update_machine_status(
            conn_local=conn_thread, 
            cursor_local=cursor_thread, 
            id_maquina=id_maquina, 
            new_status=0,  # 0 = Parada
            id_motivo_parada=ID_MOTIVO_PARADA_AUTOMATICA, 
            obs_evento="Parada automática por inatividade"
        )
        logger.info(f"Comandos para registrar parada automática para máquina {id_maquina} foram executados (aguardando commit).")
    except Exception as e:
        # Relança a exceção para que a função principal (verificar_inatividade_maquinas) possa fazer o rollback.
        logger.error(f"Erro ao preparar registro de parada automática para máquina {id_maquina}: {str(e)}", exc_info=True)
        raise



def limpar_registros_duplicados():
    """
    Identifica e corrige registros duplicados de status de máquina abertos.
    Esta função roda em um thread separado e gerencia sua própria conexão.
    """
    conn_thread = None
    try:
        conn_thread = conectar_bd()
        cursor_thread = conn_thread.cursor()
        
        cursor_thread.execute("""
            SELECT IDMaquina, COUNT(*) as NumRegistrosAtivos
            FROM TBL_StatusMaquina
            WHERE DataHoraFim IS NULL
            GROUP BY IDMaquina
            HAVING COUNT(*) > 1
        """)
        
        maquinas_com_duplicatas = cursor_thread.fetchall()
        
        for maquina in maquinas_com_duplicatas:
            id_maquina = maquina.IDMaquina
            num_registros = maquina.NumRegistrosAtivos
            
            logger.warning(f"Máquina {id_maquina} tem {num_registros} registros de status ativos. Corrigindo...")
            
            cursor_thread.execute("""
                SELECT IDRegistroStatus, Status, DataHoraInicio, DataHoraRegistro
                FROM TBL_StatusMaquina
                WHERE IDMaquina = ? AND DataHoraFim IS NULL
                ORDER BY DataHoraRegistro ASC
            """, id_maquina)
            
            registros = cursor_thread.fetchall()
            
            for i in range(len(registros) - 1):
                registro = registros[i]
                id_registro_status = registro.IDRegistroStatus
                
                # Fechar este registro com a data/hora de início do próximo registro
                data_hora_fim = registros[i + 1].DataHoraInicio
                
                cursor_thread.execute("""
                    UPDATE TBL_StatusMaquina
                    SET DataHoraFim = ?, DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, ?)
                    WHERE IDRegistroStatus = ?
                """, data_hora_fim, data_hora_fim, id_registro_status) 
                
                logger.info(f"Fechado registro de status duplicado ID {id_registro_status} para máquina {id_maquina}")
            
        conn_thread.commit()
        
    except Exception as e:
        logger.error(f"Erro ao limpar registros duplicados: {str(e)}", exc_info=True)
    finally:
        if conn_thread:
            try:
                conn_thread.close()
            except Exception as e:
                logger.error(f"Erro ao fechar conexão do thread de limpeza: {e}")

def obter_status_maquina(id_maquina, conn_local, cursor_local):
    """
    Verifica se a máquina está em operação ou parada.
    Recebe conn_local e cursor_local.
    """
    try:
        cursor_local.execute("""
            SELECT TOP 1 Status, IDMotivoParada 
            FROM TBL_StatusMaquina 
            WHERE IDMaquina = ? 
            AND DataHoraFim IS NULL
            ORDER BY DataHoraRegistro DESC
        """, id_maquina)
        
        status_row = cursor_local.fetchone()
        
        if status_row:
            status_valor = status_row.Status
            motivo_parada = status_row.IDMotivoParada
            
            if status_valor == 0 and motivo_parada == ID_MOTIVO_PARADA_AUTOMATICA:
                logger.info(f"Máquina {id_maquina} está em parada automática por inatividade")
                return False
            else:
                return status_valor == 1
        else:
            cursor_local.execute("""
                SELECT TOP 1 Status 
                FROM TBL_StatusMaquina 
                WHERE IDMaquina = ? 
                ORDER BY DataHoraRegistro DESC
            """, id_maquina)
            
            ultimo_status = cursor_local.fetchone()
            
            if ultimo_status:
                return ultimo_status.Status == 1
            else:
                return False
            
    except Exception as e:
        logger.error(f"Erro ao obter status da máquina: {str(e)}", exc_info=True)
        return False
 
def reconciliar_status_maquinas():
    """
    Reconcilia o status das máquinas: se está marcada como parada mas tem OP ativa, atualiza.
    Esta função roda em um thread separado e gerencia sua própria conexão.
    """
    conn_thread = None
    try:
        conn_thread = conectar_bd()
        cursor_thread = conn_thread.cursor()
        cursor_thread.execute("""
            SELECT M.IDMaquina, M.NomeMaquina, E.IDExecucao
            FROM TBL_Recurso M
            JOIN TBL_ExecucaoOP E ON M.IDMaquina = E.IDMaquina
            JOIN TBL_StatusMaquina S ON M.IDMaquina = S.IDMaquina
            WHERE E.Status = 'Em Execucao'
            AND S.Status = 0 -- Parada
            AND S.DataHoraFim IS NULL -- Status atual
            AND (S.IDMotivoParada IS NULL OR S.IDMotivoParada <> ?) -- Excluir paradas automáticas por inatividade para não reverter paradas manuais classificadas
            AND S.IDStatus = (
                SELECT MAX(IDStatus) 
                FROM TBL_StatusMaquina 
                WHERE IDMaquina = M.IDMaquina
            )
        """, ID_MOTIVO_PARADA_AUTOMATICA)
        
        maquinas_para_atualizar = cursor_thread.fetchall()
        
        for maquina in maquinas_para_atualizar:
            id_maquina = maquina.IDMaquina
            nome_maquina = maquina.NomeMaquina
            
            logger.info(f"Reconciliação: Máquina {nome_maquina} (ID: {id_maquina}) marcada como parada, mas tem OP ativa. Atualizando para 'Em Execução'.")
            
            # --- Chamar a função auxiliar para atualizar o status para Produzindo (Status 1) ---
            _update_machine_status(conn_thread, cursor_thread, id_maquina, 1, obs_evento="Status atualizado por reconciliação (OP ativa)")
            # -----------------------------------------------------------------------------------
            
        conn_thread.commit()
        
    except Exception as e:
        conn_thread.rollback()
        logger.error(f"Erro ao reconciliar status das máquinas: {str(e)}", exc_info=True)

@app.route('/adicionar_refugo', methods=['POST'])
@login_requerido
@permissao_requerida('/adicionar_refugo')
def adicionar_refugo():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_maquina = request.form.get('id_maquina')
        quantidade_str = request.form.get('quantidade')
        id_motivo_refugo = request.form.get('motivo_refugo')
        observacao = request.form.get('observacao', '')
        data_refugo_str = request.form.get('data_refugo')

        if not all([id_maquina, quantidade_str, id_motivo_refugo]):
            return jsonify({'success': False, 'message': 'Dados incompletos.'})

        quantidade = float(quantidade_str.replace(',', '.'))
        
        data_hora_evento = datetime.now()
        if data_refugo_str:
            try:
                data_escolhida = datetime.strptime(data_refugo_str, '%Y-%m-%d').date()
                data_hora_evento = datetime.combine(data_escolhida, datetime.now().time())
            except ValueError:
                logger.warning(f"Formato de data inválido recebido: {data_refugo_str}. Usando data/hora atual.")
        
        # --- ALTERAÇÃO 1: Busca o IDOrdemOperacao ---
        cursor_local.execute("""
            SELECT TOP 1 
                E.IDExecucao, E.IDOrdem, E.IDOperador, R.IDTipo AS IDTipoRecurso,
                E.IDOrdemOperacao -- <<< CAMPO ADICIONADO
            FROM TBL_ExecucaoOP E
            JOIN TBL_Recurso R ON E.IDMaquina = R.IDMaquina
            WHERE E.IDMaquina = ? AND E.Status = 'Em Execucao'
            ORDER BY E.DataHoraInicio DESC
        """, id_maquina)
        execucao_info = cursor_local.fetchone()
        
        if not execucao_info:
            return jsonify({'success': False, 'message': 'Nenhuma ordem de produção ativa encontrada para esta máquina.'})

        id_turno_maquina = identificar_turno_da_maquina(conn_local, cursor_local, id_maquina)
        
        cursor_local.execute("SELECT SubtraiDaProducao FROM TBL_MotivoRefugo WHERE IDMotivoRefugo = ?", id_motivo_refugo)
        motivo_info = cursor_local.fetchone()
        is_reclassificacao = motivo_info.SubtraiDaProducao if motivo_info else False

        # --- ALTERAÇÃO 2: Adiciona o IDOrdemOperacao no INSERT de REFUGO ---
        cursor_local.execute("""
            INSERT INTO VW_EventoProducaoComCicloReal (
                IDExecucao, IDOrdemProducao, IDMaquina, IDOperador, IDTurno, IDTipoRecurso,
                Quantidade, TipoValor, OrigemEvento, ObsEvento, IDMotivoRefugo, DataHoraEvento, IDTipoEvento,
                IDOrdemOperacao -- <<< COLUNA ADICIONADA
            ) VALUES (?, ?, ?, ?, ?, ?, ?, 'REFUGO', 'MANUAL', ?, ?, ?, 2, ?)
        """, (
            execucao_info.IDExecucao, execucao_info.IDOrdem, id_maquina, execucao_info.IDOperador,
            id_turno_maquina, 
            execucao_info.IDTipoRecurso, quantidade, observacao, id_motivo_refugo,
            data_hora_evento,
            execucao_info.IDOrdemOperacao # <<< VALOR ADICIONADO
        ))

        if is_reclassificacao:
            obs_estorno = f"Estorno automático por reclassificação de refugo. Motivo: {observacao}"
            # --- ALTERAÇÃO 3: Adiciona o IDOrdemOperacao no INSERT de ESTORNO ---
            cursor_local.execute("""
                INSERT INTO VW_EventoProducaoComCicloReal (
                    IDExecucao, IDOrdemProducao, IDMaquina, IDOperador, IDTurno, IDTipoRecurso,
                    Quantidade, TipoValor, OrigemEvento, ObsEvento, IDMotivoRefugo, DataHoraEvento, IDTipoEvento,
                    IDOrdemOperacao -- <<< COLUNA ADICIONADA
                ) VALUES (?, ?, ?, ?, ?, ?, ?, 'ESTORNO', 'AUTOMATICO_REFUGO', ?, ?, ?, 2, ?)
            """, (
                execucao_info.IDExecucao, execucao_info.IDOrdem, id_maquina, execucao_info.IDOperador,
                id_turno_maquina,
                execucao_info.IDTipoRecurso, 
                -quantidade, 
                obs_estorno, id_motivo_refugo, data_hora_evento,
                execucao_info.IDOrdemOperacao # <<< VALOR ADICIONADO
            ))
            message = 'Refugo lançado como RECLASSIFICAÇÃO (debitado das peças boas).'
        else:
            message = 'Refugo lançado como PERDA DIRETA.'

        conn_local.commit()
        return jsonify({'success': True, 'message': message})
    
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao adicionar refugo manual: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Erro interno no servidor.'})
    
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/api/ops_concluidas_recentes/<int:id_maquina_contexto>')
@login_requerido
def api_ops_concluidas_recentes(id_maquina_contexto):
    conn_local = None
    try:
        DIAS_RETROATIVOS = 7
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        query = """
            SELECT 
                MAX(EX.IDExecucao) as IDExecucao,
                O.CodigoOrdem,
                P.NomeProduto,
                P.CodigoProduto,
                ISNULL(CAST(MAX(OPO.NumeroOperacao) AS VARCHAR(20)) + ' - ' + ISNULL(MAX(OPO.Descricao), ''), 'N/A') as OperacaoDesc,
                MIN(EX.DataHoraInicio) as DataHoraInicio,
                MAX(EX.DataHoraFim) as DataHoraFim,
                
                -- Soma da produção real (Eventos)
                (
                    SELECT ISNULL(SUM(EV.Quantidade), 0)
                    FROM VW_EventoProducaoComCicloReal EV
                    WHERE EV.IDOrdemProducao = EX.IDOrdem 
                      AND EV.IDMaquina = EX.IDMaquina
                      AND EV.TipoValor IN ('BOA', 'ESTORNO')
                ) as QuantidadeProduzida,
                
                MAX(EX.IDOrdemOperacao) as IDOrdemOperacao,
                EX.IDOrdem,
                MAX(R.IDTipo) AS IDTipoRecurso,
                MAX(EX.IDTurno) as IDTurno,
                MAX(EX.IDOperador) as IDOperador,
                EX.IDMaquina,
                R.NomeMaquina
            FROM TBL_ExecucaoOP EX
            JOIN TBL_OrdemProducao O ON EX.IDOrdem = O.IDOrdem
            JOIN TBL_Recurso R ON EX.IDMaquina = R.IDMaquina
            JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
            LEFT JOIN TBL_OrdemProducao_Operacoes OPO ON EX.IDOrdemOperacao = OPO.IDOrdemOperacao
            WHERE 
                EX.IDMaquina = ?  -- <<< FILTRO DE MÁQUINA RECOLOCADO AQUI
                AND (EX.Status = 'Finalizada' OR EX.Status LIKE '%Finalizada%')
                AND EX.DataHoraFim >= DATEADD(day, -?, GETDATE())
                AND EX.DataHoraFim IS NOT NULL 
            GROUP BY 
                EX.IDOrdem, O.CodigoOrdem, P.NomeProduto, P.CodigoProduto, EX.IDMaquina, R.NomeMaquina
            ORDER BY 
                MAX(EX.DataHoraFim) DESC
        """
        
        # Passamos DOIS parâmetros agora: ID da Máquina e Dias Retroativos
        cursor_local.execute(query, (id_maquina_contexto, DIAS_RETROATIVOS))
        
        ops = []
        for row in cursor_local.fetchall():
            fim_formatado = row.DataHoraFim.strftime('%d/%m %H:%M') if row.DataHoraFim else 'Em andamento'
            
            ops.append({
                'id_execucao': row.IDExecucao,
                'codigo_ordem': row.CodigoOrdem,
                'produto': f"{row.CodigoProduto} - {row.NomeProduto}",
                'operacao': row.OperacaoDesc,
                'inicio': row.DataHoraInicio.strftime('%d/%m %H:%M'),
                'fim': fim_formatado,
                'qtd_produzida': float(row.QuantidadeProduzida or 0),
                'id_ordem_operacao': row.IDOrdemOperacao,
                'id_ordem': row.IDOrdem,
                'id_tipo_recurso': row.IDTipoRecurso,
                'id_turno': row.IDTurno,
                'id_operador_original': row.IDOperador,
                'id_maquina_original': row.IDMaquina,
                'nome_maquina': row.NomeMaquina
            })
            
        return jsonify({
            'success': True, 
            'ops': ops,
            'dias_retroativos': DIAS_RETROATIVOS 
        })
        
    except Exception as e:
        logger.error(f"ERRO SQL EM api_ops_concluidas_recentes: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': f'Erro técnico: {str(e)}'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/api/salvar_refugo_retroativo_lote', methods=['POST'])
@login_requerido
def api_salvar_refugo_retroativo_lote():
    conn_local = None
    try:
        data = request.json
        id_maquina = data.get('id_maquina')
        dados_execucao = data.get('dados_execucao') # Objeto com IDs da OP original
        lista_refugos = data.get('lista_refugos') # Array de objetos {motivo, quantidade, obs}
        
        if not id_maquina or not dados_execucao or not lista_refugos:
            return jsonify({'success': False, 'message': 'Dados incompletos.'}), 400

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        id_usuario_logado = session.get('usuario_id')
        data_hora_registro = datetime.now()

        for item in lista_refugos:
            qtd = float(item['quantidade'])
            id_motivo = int(item['id_motivo'])
            obs = item.get('observacao', '')
            
            # Monta observação indicando que é retroativo
            obs_final = f"[RETROATIVO] {obs}"

            # Verifica se o motivo é de reclassificação (subtrai da produção boa)
            cursor_local.execute("SELECT SubtraiDaProducao FROM TBL_MotivoRefugo WHERE IDMotivoRefugo = ?", id_motivo)
            motivo_info = cursor_local.fetchone()
            is_reclassificacao = motivo_info.SubtraiDaProducao if motivo_info else False

            # 1. Insere o Refugo
            cursor_local.execute("""
                INSERT INTO VW_EventoProducaoComCicloReal (
                    IDExecucao, IDOrdemProducao, IDMaquina, IDOperador, IDTurno, IDTipoRecurso,
                    Quantidade, TipoValor, OrigemEvento, ObsEvento, IDMotivoRefugo, DataHoraEvento, IDTipoEvento,
                    IDOrdemOperacao
                ) VALUES (?, ?, ?, ?, ?, ?, ?, 'REFUGO', 'MANUAL_RETRO', ?, ?, ?, 2, ?)
            """, (
                dados_execucao['id_execucao'], 
                dados_execucao['id_ordem'], 
                id_maquina, 
                id_usuario_logado, # Quem está lançando agora, não o operador original
                dados_execucao['id_turno'], # Mantém o turno da produção original para contabilidade
                dados_execucao['id_tipo_recurso'], 
                qtd, 
                obs_final, 
                id_motivo, 
                data_hora_registro, 
                dados_execucao['id_ordem_operacao']
            ))

            # 2. Se for reclassificação, insere o Estorno das boas
            if is_reclassificacao:
                cursor_local.execute("""
                    INSERT INTO VW_EventoProducaoComCicloReal (
                        IDExecucao, IDOrdemProducao, IDMaquina, IDOperador, IDTurno, IDTipoRecurso,
                        Quantidade, TipoValor, OrigemEvento, ObsEvento, IDMotivoRefugo, DataHoraEvento, IDTipoEvento,
                        IDOrdemOperacao
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, 'ESTORNO', 'AUTO_RETRO', ?, ?, ?, 2, ?)
                """, (
                    dados_execucao['id_execucao'], 
                    dados_execucao['id_ordem'], 
                    id_maquina, 
                    id_usuario_logado,
                    dados_execucao['id_turno'], 
                    dados_execucao['id_tipo_recurso'], 
                    -qtd, 
                    f"Estorno automático por refugo retroativo. Motivo: {obs_final}", 
                    id_motivo, 
                    data_hora_registro, 
                    dados_execucao['id_ordem_operacao']
                ))

        conn_local.commit()
        return jsonify({'success': True, 'message': f'{len(lista_refugos)} lançamentos de refugo registrados com sucesso!'})

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao salvar refugo retroativo: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Erro interno ao salvar dados.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)            
            

@app.route('/cadastro_motivo_alarme', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_motivo_alarme')
def cadastro_motivo_alarme():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_motivo = request.args.get('id')
        motivo_editar = None
        
        tipos_alarme = ['Crítico', 'Alerta', 'Informativo', 'Manutenção', 'Segurança']

        if request.method == 'POST':
            id_motivo_form = request.form.get('id_motivo')
            codigo = request.form['codigo']
            nome = request.form['nome']
            descricao = request.form['descricao']
            tipo_alarme = request.form['tipo_alarme']
            id_grupo = request.form['id_grupo']
            ativo = 1 if 'ativo' in request.form else 0
            comentario_obrigatorio = 1 if 'comentario_obrigatorio' in request.form else 0
            
            # --- INÍCIO DA ALTERAÇÃO ---
            # Captura o valor da nova flag 'Exige Reconhecimento'
            exige_reconhecimento = 1 if 'exige_reconhecimento' in request.form else 0
            # --- FIM DA ALTERAÇÃO ---

            if id_motivo_form:
                # --- ALTERAÇÃO: Adiciona a nova coluna ao UPDATE ---
                cursor_local.execute("""
                    UPDATE TBL_MotivoAlarme
                    SET Codigo = ?, Nome = ?, Descricao = ?, TipoAlarme = ?, 
                        IDGrupoAlarme = ?, Ativo = ?, ComentarioObrigatorio = ?, ExigeReconhecimento = ?, DataAtualizacao = GETDATE()
                    WHERE IDMotivoAlarme = ?
                """, (codigo, nome, descricao, tipo_alarme, id_grupo, ativo, comentario_obrigatorio, exige_reconhecimento, id_motivo_form))
                flash("Motivo de alarme atualizado com sucesso!", "success")
            else:
                # --- ALTERAÇÃO: Adiciona a nova coluna ao INSERT ---
                cursor_local.execute("""
                    INSERT INTO TBL_MotivoAlarme 
                    (Codigo, Nome, Descricao, TipoAlarme, IDGrupoAlarme, Ativo, ComentarioObrigatorio, ExigeReconhecimento, DataCriacao)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, GETDATE())
                """, (codigo, nome, descricao, tipo_alarme, id_grupo, ativo, comentario_obrigatorio, exige_reconhecimento))
                flash("Motivo de alarme cadastrado com sucesso!", "success")

            conn_local.commit()
            return redirect(url_for('cadastro_motivo_alarme'))

        # A lógica GET não precisa de alteração, pois SELECT * já busca a nova coluna
        if id_motivo:
            cursor_local.execute("SELECT * FROM TBL_MotivoAlarme WHERE IDMotivoAlarme = ?", (id_motivo,))
            motivo_editar = cursor_local.fetchone()

        cursor_local.execute("SELECT IDGrupoAlarme, Nome FROM TBL_GrupoAlarme WHERE Ativo = 1 ORDER BY Nome")
        grupos = cursor_local.fetchall()

        cursor_local.execute("""
            SELECT M.*, G.Nome AS NomeGrupo
            FROM TBL_MotivoAlarme M
            LEFT JOIN TBL_GrupoAlarme G ON M.IDGrupoAlarme = G.IDGrupoAlarme
            ORDER BY M.Nome
        """)
        motivos = cursor_local.fetchall()

        return render_template('cadastro_motivo_alarme.html', 
                              motivos=motivos, 
                              motivo_editar=motivo_editar, 
                              grupos=grupos,
                              tipos_alarme=tipos_alarme)
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em cadastro_motivo_alarme: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar motivos de alarme.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/alterar_status_motivo_alarme/<int:id_motivo>/<int:status>')
@login_requerido
@permissao_requerida('/cadastro_motivo_alarme')
def alterar_status_motivo_alarme(id_motivo, status):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("""
            UPDATE TBL_MotivoAlarme
            SET Ativo = ?, DataAtualizacao = GETDATE()
            WHERE IDMotivoAlarme = ?
        """, (status, id_motivo))
        conn_local.commit()
        flash("Status do motivo de alarme alterado!", "success")
        return redirect(url_for('cadastro_motivo_alarme'))
    except Exception as e:
        if conn_local:
            conn_local.rollback()
        logger.error(f"Erro em alterar_status_motivo_alarme: {e}", exc_info=True)
        flash("Ocorreu um erro ao alterar o status do motivo de alarme.", "error")
        return redirect(url_for('cadastro_motivo_alarme'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
def converter_tempo_ciclo_para_segundos(valor, unidade):
    valor = float(valor)
    if unidade == 's/un':
        return valor
    elif unidade == 'min/un':
        return valor * 60
    elif unidade == 'h/un':
        return valor * 3600
    
    elif unidade in ['un/min', 'mt/min']: # Adicionado 'mt/min'
        return 60 / valor if valor > 0 else 0
    elif unidade in ['un/h', 'mt/h']: # Adicionado 'mt/h' por consistência
        return 3600 / valor if valor > 0 else 0
    return 0

# Em planner_app.py

@app.route('/ferramenta_produto', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/ferramenta_produto')
def ferramenta_produto():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            id_recurso_produto = request.form.get('id_recurso_produto') # Pega o ID para saber se é edição
            id_recurso = request.form.get('id_recurso')
            id_produto = request.form.get('id_produto')
            tempo_ciclo = request.form.get('tempo_ciclo')
            unidade_tempo_ciclo = request.form.get('unidade_tempo_ciclo')
            fator_multiplicacao = request.form.get('fator_multiplicacao', 1.0)
            
            # +++++ CAPTURA O NOVO CAMPO DE SETUP +++++
            tempo_setup_minutos = float(request.form.get('tempo_setup', 0))
            tempo_setup_segundos = tempo_setup_minutos * 60

            if not all([id_recurso, id_produto, tempo_ciclo, unidade_tempo_ciclo]):
                flash("Todos os campos são obrigatórios.", "error")
                return redirect(url_for('ferramenta_produto'))

            tempo_padrao_segundos = converter_tempo_ciclo_para_segundos(tempo_ciclo, unidade_tempo_ciclo)

            if id_recurso_produto: # ATUALIZAÇÃO
                cursor_local.execute("""
                    UPDATE TBL_RecursoProduto
                    SET IDRecurso = ?, IDProduto = ?, TempoCiclo = ?, UnidadeTempoCiclo = ?, 
                        TempoCicloPadraoSegundos = ?, FatorMultiplicacao = ?, TempoSetupSegundos = ?, 
                        DataAtualizacao = GETDATE()
                    WHERE IDRecursoProduto = ?
                """, (id_recurso, id_produto, tempo_ciclo, unidade_tempo_ciclo, tempo_padrao_segundos, 
                      fator_multiplicacao, tempo_setup_segundos, id_recurso_produto))
                flash("Configuração Ferramenta x Produto atualizada com sucesso!", "success")
            else: # NOVO CADASTRO
                # Verifica se a combinação já existe para evitar duplicatas
                cursor_local.execute(
                    "SELECT IDRecursoProduto FROM TBL_RecursoProduto WHERE IDRecurso = ? AND IDProduto = ?",
                    (id_recurso, id_produto)
                )
                if cursor_local.fetchone():
                    flash("Esta combinação de Recurso e Produto já existe. Edite o registro existente.", "warning")
                else:
                    cursor_local.execute("""
                        INSERT INTO TBL_RecursoProduto
                        (IDRecurso, IDProduto, TempoCiclo, UnidadeTempoCiclo, TempoCicloPadraoSegundos, FatorMultiplicacao, TempoSetupSegundos)
                        VALUES (?, ?, ?, ?, ?, ?, ?)
                    """, (id_recurso, id_produto, tempo_ciclo, unidade_tempo_ciclo, tempo_padrao_segundos, fator_multiplicacao, tempo_setup_segundos))
                    flash("Configuração Ferramenta x Produto cadastrada com sucesso!", "success")

            conn_local.commit()
            return redirect(url_for('ferramenta_produto'))

        # A lógica GET foi atualizada para buscar o novo campo
        cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina")
        recursos = cursor_local.fetchall()
        
        cursor_local.execute("SELECT IDProduto, NomeProduto, CodigoProduto FROM TBL_Produto WHERE Habilitado = 1 ORDER BY NomeProduto")
        produtos = cursor_local.fetchall()

        cursor_local.execute("""
            SELECT
                RP.IDRecursoProduto, RP.TempoCiclo, RP.UnidadeTempoCiclo, RP.FatorMultiplicacao,
                RP.TempoSetupSegundos, -- << CAMPO ADICIONADO
                R.NomeMaquina, P.NomeProduto, P.CodigoProduto,
                RP.IDRecurso, RP.IDProduto
            FROM TBL_RecursoProduto RP
            JOIN TBL_Recurso R ON RP.IDRecurso = R.IDMaquina
            JOIN TBL_Produto P ON RP.IDProduto = P.IDProduto
            ORDER BY R.NomeMaquina, P.NomeProduto
        """)
        configuracoes = cursor_local.fetchall()

        return render_template('ferramenta_produto.html',
                               recursos=recursos,
                               produtos=produtos,
                               configuracoes=configuracoes)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em /ferramenta_produto: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar a página.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# Rota para deletar uma configuração
@app.route('/ferramenta_produto/deletar/<int:id_config>', methods=['POST'])
@login_requerido
@permissao_requerida('/ferramenta_produto')
def deletar_ferramenta_produto(id_config):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        cursor_local.execute("DELETE FROM TBL_RecursoProduto WHERE IDRecursoProduto = ?", (id_config,))
        conn_local.commit()
        flash("Configuração removida com sucesso.", "success")
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao deletar configuração: {e}", exc_info=True)
        flash("Erro ao remover configuração.", "error")
    finally:
        if conn_local:
            devolver_conexao(conn_local)
    return redirect(url_for('ferramenta_produto'))             

@app.route('/adicionar_producao', methods=['POST'])
@login_requerido
@permissao_requerida('/adicionar_producao')
def adicionar_producao():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        id_maquina = request.form.get('id_maquina', type=int)
        quantidade_form = request.form.get('quantidade', type=int)
        observacao = request.form.get('observacao')
        tipo_producao = request.form.get('tipo') 
        
        if not id_maquina or not quantidade_form:
            return jsonify({'success': False, 'message': 'Dados incompletos.'})

        # --- ALTERAÇÃO 1: Busca o IDOrdemOperacao ---
        cursor_local.execute("""
            SELECT TOP 1 
                E.IDExecucao, E.IDOrdem, E.IDOperador, E.IDTurno, R.IDTipo AS IDTipoRecurso,
                O.IDProduto,
                E.IDOrdemOperacao -- <<< CAMPO ADICIONADO
            FROM TBL_ExecucaoOP E
            JOIN TBL_Recurso R ON E.IDMaquina = R.IDMaquina
            JOIN TBL_OrdemProducao O ON E.IDOrdem = O.IDOrdem
            WHERE E.IDMaquina = ? AND E.Status = 'Em Execucao'
            ORDER BY E.DataHoraInicio DESC
        """, id_maquina)
        
        execucao_info = cursor_local.fetchone()
        if not execucao_info:
            return jsonify({'success': False, 'message': 'Nenhuma ordem de produção ativa encontrada para esta máquina.'})
        
        quantidade_final = quantidade_form
        if tipo_producao == 'caixa':
            id_produto = execucao_info.IDProduto
            cursor_local.execute("SELECT UnidadesPorCaixa FROM TBL_Produto WHERE IDProduto = ?", id_produto)
            produto_info = cursor_local.fetchone()
            
            unidades_por_caixa = 1
            if produto_info and produto_info.UnidadesPorCaixa > 0:
                unidades_por_caixa = produto_info.UnidadesPorCaixa

            quantidade_final = quantidade_form * unidades_por_caixa

        # --- ALTERAÇÃO 2: Adiciona o IDOrdemOperacao no INSERT ---
        cursor_local.execute("""
            INSERT INTO VW_EventoProducaoComCicloReal (
                IDExecucao, IDOrdemProducao, IDMaquina, IDOperador, IDTurno, IDTipoRecurso,
                Quantidade, TipoValor, OrigemEvento, ObsEvento, DataHoraEvento, IDTipoEvento,
                IDOrdemOperacao -- <<< COLUNA ADICIONADA
            ) VALUES (?, ?, ?, ?, ?, ?, ?, 'BOA', 'MANUAL', ?, GETDATE(), 1, ?)
        """, (
            execucao_info.IDExecucao, execucao_info.IDOrdem, id_maquina, execucao_info.IDOperador,
            execucao_info.IDTurno, execucao_info.IDTipoRecurso, 
            quantidade_final,
            observacao,
            execucao_info.IDOrdemOperacao # <<< VALOR ADICIONADO
        ))

        conn_local.commit()
        return jsonify({'success': True, 'message': 'Produção adicionada com sucesso!'})

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao adicionar produção manual: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Erro interno no servidor.'})
    finally:
        if conn_local:
            devolver_conexao(conn_local)


# --- Funções de Threading e Inicialização ---

def verificar_inatividade_periodicamente():
    """Loop para verificar inatividade das máquinas periodicamente."""
    while True:
        try:
            verificar_inatividade_maquinas() # Esta função gerencia sua própria conexão
            time.sleep(5)
        except Exception as e:
            logger.error(f"Erro no thread de verificação de inatividade: {str(e)}", exc_info=True)
            time.sleep(5) # Continua tentando mesmo em caso de erro

def limpar_registros_duplicados_periodicamente():
    """Loop para limpar registros duplicados periodicamente."""
    while True:
        try:
            limpar_registros_duplicados() # Esta função gerencia sua própria conexão
            time.sleep(60)
        except Exception as e:
            logger.error(f"Erro ao executar limpeza periódica: {str(e)}", exc_info=True)
            time.sleep(60)


# --- Funções de Threading e Inicialização ---

# ... (suas outras funções de threading e inicialização de threads)

# Iniciar os threads de verificação
thread_inatividade = threading.Thread(target=verificar_inatividade_periodicamente, daemon=True)
thread_inatividade.start()

thread_limpeza = threading.Thread(target=limpar_registros_duplicados_periodicamente, daemon=True)
thread_limpeza.start()

# Iniciar o buffer agrupado (para gravação de produção consolidada)
def start_buffer_timer():
    thread_gravar_buffer = threading.Timer(300.0, gravar_buffer_agrupado) # A cada 5 minutos
    thread_gravar_buffer.daemon = True
    thread_gravar_buffer.start()
    logger.info("Thread do timer de gravação do buffer iniciada.")

start_buffer_timer()


# Em planner_app.py, substitua esta função

def _consumir_componentes_por_producao(cursor_local, id_execucao, id_produto, quantidade_produzida, id_ordem_producao):
    """
    Função auxiliar para consumir matérias-primas.
    VERSÃO CORRIGIDA: Garante que um erro seja gerado em caso de estoque insuficiente.
    """
    try:
        cursor_local.execute("""
            SELECT PC.IDMateriaPrima, PC.QuantidadeNecessaria, MP.NomeMateriaPrima, 
                   MP.GeraAlertaEstoque, MP.ConsumoDiario, MP.PrazoEntregaDias, MP.AlertaCompraEnviado, MP.PermiteEstorno
            FROM TBL_ProdutoComponente PC
            JOIN TBL_MateriaPrima MP ON PC.IDMateriaPrima = MP.IDMateriaPrima
            WHERE PC.IDProduto = ?
        """, (id_produto,))
        componentes_necessarios = cursor_local.fetchall()

        if not componentes_necessarios:
            logger.warning(f"Produto ID {id_produto} não possui estrutura (BOM) definida. Nenhum material foi consumido.")
            return True

        for componente in componentes_necessarios:
            id_materia_prima = componente.IDMateriaPrima
            nome_materia_prima = componente.NomeMateriaPrima
            quantidade_total_necessaria = float(componente.QuantidadeNecessaria) * quantidade_produzida

            if quantidade_total_necessaria <= 0:
                continue

            logger.info(f"Processando consumo para o componente '{nome_materia_prima}' (ID: {id_materia_prima}). Necessidade total: {quantidade_total_necessaria}")

            cursor_local.execute("""
                SELECT IDEstoque, QuantidadeDisponivel, Lote, IDFornecedor, NumeroNotaFiscal
                FROM TBL_EstoqueMP WITH (UPDLOCK) 
                WHERE IDMateriaPrima = ? AND QuantidadeDisponivel > 0 
                ORDER BY DataEntrada ASC
            """, (id_materia_prima,))
            lotes_disponiveis = cursor_local.fetchall()

            estoque_total_disponivel = sum(float(lote.QuantidadeDisponivel) for lote in lotes_disponiveis)
            
            # --- LÓGICA DE BLOQUEIO RESTAURADA ---
            if estoque_total_disponivel < quantidade_total_necessaria:
                # Esta linha gera o erro que interrompe o processo, como deveria.
                raise EstoqueInsuficienteError(f"Estoque insuficiente para '{nome_materia_prima}'. Necessário: {quantidade_total_necessaria:.2f}, Disponível: {estoque_total_disponivel:.2f}")

            quantidade_restante_a_consumir = quantidade_total_necessaria
            
            for lote in lotes_disponiveis:
                if quantidade_restante_a_consumir <= 0:
                    break

                id_estoque_atual = lote.IDEstoque
                lote_atual = lote.Lote
                disponivel_neste_lote = float(lote.QuantidadeDisponivel)
                id_fornecedor_do_lote = lote.IDFornecedor
                nf_do_lote = lote.NumeroNotaFiscal
                
                quantidade_a_consumir_deste_lote = min(quantidade_restante_a_consumir, disponivel_neste_lote)
                nova_quantidade_no_lote = disponivel_neste_lote - quantidade_a_consumir_deste_lote
                
                cursor_local.execute("UPDATE TBL_EstoqueMP SET QuantidadeDisponivel = ? WHERE IDEstoque = ?", (nova_quantidade_no_lote, id_estoque_atual))
                cursor_local.execute("""
                    INSERT INTO TBL_LogMovimentacaoEstoque
                    (IDEstoqueMP, IDMateriaPrima, Lote, TipoMovimento, Quantidade, IDExecucaoOP, Observacao, IDFornecedor, NumeroNotaFiscal)
                    VALUES (?, ?, ?, 'CONSUMO_PRODUCAO', ?, ?, ?, ?, ?)
                """, (id_estoque_atual, id_materia_prima, lote_atual, -quantidade_a_consumir_deste_lote, id_execucao, f"Consumo para OP {id_ordem_producao}", id_fornecedor_do_lote, nf_do_lote))
                
                quantidade_restante_a_consumir -= quantidade_a_consumir_deste_lote
            
            # Lógica de alerta de compra (continua a mesma)
            if componente.GeraAlertaEstoque and componente.ConsumoDiario and componente.ConsumoDiario > 0 and componente.PrazoEntregaDias and componente.PrazoEntregaDias > 0 and not componente.AlertaCompraEnviado:
                # ... (código de alerta)
                pass

        return True
    
    except EstoqueInsuficienteError:
        raise # Apenas repassa o erro para a função 'finalizar_op' poder capturá-lo
    except Exception as e:
        logger.error(f"Erro na função _consumir_componentes_por_producao: {e}", exc_info=True)
        raise

def enviar_email_alerta_compra_mp(nome_materia_prima, saldo_atual, ponto_ressuprimento, consumo_diario, prazo_entrega):
    def _enviar_thread():
        conn_local = None
        server = None 
        try:
            conn_local = obter_conexao()
            cursor_local = conn_local.cursor()

            cursor_local.execute("""
                SELECT DISTINCT U.Email
                FROM TBL_Usuario U
                JOIN TBL_GrupoUsuario GU ON U.IDGrupo = GU.IDGrupo
                WHERE GU.RecebeAlertaEstoque = 1 AND U.Ativo = 1 AND U.Email IS NOT NULL AND U.Email <> ''
            """)
            destinatarios = [row.Email for row in cursor_local.fetchall()]
            
            if not destinatarios:
                logger.warning(f"Alerta de compra para '{nome_materia_prima}', mas nenhum grupo configurado.")
                return

            config_keys = "('SMTP_HOST', 'SMTP_PORT', 'SMTP_USER', 'SMTP_PASSWORD', 'SMTP_USE_TLS', 'SMTP_SENDER_EMAIL', 'SMTP_SENDER_NAME')"
            cursor_local.execute(f"SELECT ChaveConfig, ValorConfig FROM TBL_Configuracao WHERE ChaveConfig IN {config_keys}")
            smtp_config = {row.ChaveConfig: row.ValorConfig for row in cursor_local.fetchall()}
            
            msg = MIMEMultipart()
            sender_name = smtp_config.get('SMTP_SENDER_NAME', 'Planner Alertas')
            sender_email = smtp_config.get('SMTP_SENDER_EMAIL')
            msg['From'] = formataddr((sender_name, sender_email))
            msg['To'] = ", ".join(destinatarios)
            
            assunto = f"ALERTA DE COMPRA: A matéria-prima '{nome_materia_prima}' atingiu o ponto de ressuprimento"
            
            # --- INÍCIO DA CORREÇÃO ---
            # A linha abaixo estava faltando. Ela define o assunto no e-mail.
            msg['Subject'] = assunto
            # --- FIM DA CORREÇÃO ---
    
            saldo_fmt = ("%g" % saldo_atual).replace('.', ',')
            ponto_fmt = ("%g" % ponto_ressuprimento).replace('.', ',')
            consumo_fmt = ("%g" % consumo_diario).replace('.', ',')

            body_html = f"""
            <html>
                <head>
                    <style>
                        body {{ font-family: Arial, sans-serif; }}
                        .container {{ max-width: 600px; margin: 20px auto; padding: 20px; border: 1px solid #ddd; border-radius: 8px; }}
                        .header {{ background-color: #0277bd; color: white; padding: 10px 20px; border-radius: 5px 5px 0 0; text-align: center;}}
                        h2 {{ margin-top: 0; }}
                        ul {{ list-style-type: none; padding: 0; }}
                        li {{ background-color: #f2f2f2; margin-bottom: 5px; padding: 10px; border-radius: 4px; }}
                        li strong {{ color: #0277bd; }}
                    </style>
                </head>
                <body>
                    <div class="container">
                        <div class="header">
                            <h2>Notificação de Ponto de Ressuprimento</h2>
                        </div>
                        <p>A matéria-prima <strong>{nome_materia_prima}</strong> atingiu o seu ponto de ressuprimento e uma nova compra é recomendada.</p>
                        <hr>
                        <p><strong>Detalhes do Alerta:</strong></p>
                        <ul>
                            <li><strong>Saldo Atual em Estoque:</strong> {saldo_fmt} unidades</li>
                            <li><strong>Ponto de Ressuprimento Calculado:</strong> {ponto_fmt} unidades</li>
                        </ul>
                        <p><strong>Dados Utilizados no Cálculo:</strong></p>
                        <ul>
                            <li><strong>Consumo Diário Estimado:</strong> {consumo_fmt} unidades/dia</li>
                            <li><strong>Prazo de Entrega do Fornecedor:</strong> {prazo_entrega} dias</li>
                        </ul>
                        <p style="font-size: 0.9em; color: #777;">Este alerta foi enviado porque o saldo atual é igual ou inferior ao ponto de ressuprimento. Ele não será enviado novamente até que uma nova entrada de estoque para este item seja registada.</p>
                    </div>
                </body>
            </html>
            """
            msg.attach(MIMEText(body_html, 'html'))
            
            smtp_host = smtp_config.get('SMTP_HOST')
            smtp_port = int(smtp_config.get('SMTP_PORT'))
            logger.info(f"Tentando conectar ao servidor SMTP: {smtp_host}:{smtp_port}")
            server = smtplib.SMTP(smtp_host, smtp_port, timeout=10) 
            
            if smtp_config.get('SMTP_USE_TLS', 'false').lower() == 'true':
                logger.info("Iniciando conexão TLS...")
                server.starttls()
            
            logger.info("Realizando login no servidor SMTP...")
            server.login(smtp_config.get('SMTP_USER'), smtp_config.get('SMTP_PASSWORD'))
            
            logger.info(f"Enviando e-mail para: {destinatarios}")
            server.sendmail(sender_email, destinatarios, msg.as_string())
            
            logger.info(f"E-mail de alerta de COMPRA para '{nome_materia_prima}' enviado com sucesso.")
        
        except smtplib.SMTPAuthenticationError as e:
            logger.error(f"Falha no envio de e-mail: Erro de autenticação. Verifique o usuário e a senha (ou Senha de App). Detalhe: {e}")
        except ConnectionRefusedError:
            logger.error(f"Falha no envio de e-mail: Conexão recusada pelo servidor {smtp_config.get('SMTP_HOST')}:{smtp_config.get('SMTP_PORT')}. Verifique o host, a porta e as regras de firewall.")
        except smtplib.SMTPServerDisconnected:
            logger.error("Falha no envio de e-mail: O servidor desconectou. Verifique se a conexão inicial (host/porta) foi bem-sucedida.")
        except Exception as e:
            logger.error(f"Falha CRÍTICA ao enviar e-mail de alerta de COMPRA: {e}", exc_info=True)
        finally:
            if server:
                try:
                    server.quit()
                except Exception:
                    pass 
            if conn_local:
                devolver_conexao(conn_local)
                
    threading.Thread(target=_enviar_thread).start()
    
# Em planner_app.py, substitua esta função inteira:

def enviar_email_alerta_estoque_baixo(nome_materia_prima, saldo_atual, limite_alerta):
    """
    Busca os destinatários com a flag 'RecebeAlertaEstoque' e envia o e-mail
    de alerta de estoque baixo em uma nova thread para não travar a aplicação.
    """
    def _enviar_thread():
        conn_local = None
        try:
            conn_local = obter_conexao()
            cursor_local = conn_local.cursor()
            
            # Busca os destinatários que têm a flag "RecebeAlertaEstoque" ativa
            cursor_local.execute("""
                SELECT DISTINCT U.Email
                FROM TBL_Usuario U
                JOIN TBL_GrupoUsuario GU ON U.IDGrupo = GU.IDGrupo
                WHERE GU.RecebeAlertaEstoque = 1 AND U.Ativo = 1 AND U.Email IS NOT NULL AND U.Email <> ''
            """)
            
            destinatarios = [row.Email for row in cursor_local.fetchall()]
            
            if not destinatarios:
                logger.warning(f"Alerta de estoque baixo para '{nome_materia_prima}', mas nenhum grupo de usuário está configurado para receber esta notificação.")
                return

            # --- Lógica de envio de e-mail (reutilizando a sua estrutura) ---
            config_keys = "('SMTP_HOST', 'SMTP_PORT', 'SMTP_USER', 'SMTP_PASSWORD', 'SMTP_USE_TLS', 'SMTP_SENDER_EMAIL', 'SMTP_SENDER_NAME')"
            cursor_local.execute(f"SELECT ChaveConfig, ValorConfig FROM TBL_Configuracao WHERE ChaveConfig IN {config_keys}")
            smtp_config = {row.ChaveConfig: row.ValorConfig for row in cursor_local.fetchall()}

            msg = MIMEMultipart()
            sender_name = smtp_config.get('SMTP_SENDER_NAME', 'Planner Alertas')
            sender_email = smtp_config.get('SMTP_SENDER_EMAIL')
            
            msg['From'] = formataddr((sender_name, sender_email))
            msg['To'] = ", ".join(destinatarios)
            msg['Subject'] = f"ALERTA DE ESTOQUE BAIXO: {nome_materia_prima}"

            # --- INÍCIO DA CORREÇÃO NA FORMATAÇÃO ---
            # Troca :.2f por %g para remover zeros desnecessários
            saldo_formatado = ("%g" % saldo_atual).replace('.', ',')
            limite_formatado = ("%g" % limite_alerta).replace('.', ',')
            # --- FIM DA CORREÇÃO ---

            body_html = f"""
            <html>
                <body style="font-family: Arial, sans-serif;">
                    <h2 style="color: #ff9800;">Notificação de Estoque Baixo</h2>
                    <p>A matéria-prima <strong>{nome_materia_prima}</strong> atingiu um nível crítico no chão de fábrica.</p>
                    <ul>
                        <li><strong>Saldo Atual:</strong> {saldo_formatado} unidades</li>
                        <li><strong>Nível Mínimo de Alerta:</strong> {limite_formatado} unidades</li>
                    </ul>
                    <p>Por favor, providencie a reposição do material para evitar paradas na produção.</p>
                    <p style="font-size: 0.8em; color: #777;">Este é um e-mail automático. Por favor, não responda.</p>
                </body>
            </html>
            """
            msg.attach(MIMEText(body_html, 'html'))

            server = smtplib.SMTP(smtp_config.get('SMTP_HOST'), int(smtp_config.get('SMTP_PORT')))
            if smtp_config.get('SMTP_USE_TLS', 'false').lower() == 'true':
                server.starttls()
            server.login(smtp_config.get('SMTP_USER'), smtp_config.get('SMTP_PASSWORD'))
            server.sendmail(sender_email, destinatarios, msg.as_string())
            server.quit()

            logger.info(f"E-mail de alerta de estoque para '{nome_materia_prima}' enviado com sucesso para {len(destinatarios)} destinatário(s).")

        except Exception as e:
            logger.error(f"Falha CRÍTICA ao enviar e-mail de alerta de estoque: {e}", exc_info=True)
        finally:
            if conn_local:
                devolver_conexao(conn_local)
                
    threading.Thread(target=_enviar_thread).start()       
        
@app.route('/estoque_dashboard')
@login_requerido
@permissao_requerida('/estoque_dashboard') # Lembre-se de cadastrar esta permissão!
def estoque_dashboard():
    # No futuro, podemos adicionar lógica aqui para buscar KPIs de estoque.
    # Por enquanto, ela apenas renderiza a página do hub de estoque.
    return render_template('estoque_dashboard.html')        
# ###############################################################
# ##### INÍCIO DO NOVO BLOCO - CONTROLE DE ESTOQUE (MATÉRIA-PRIMA) #####
# ###############################################################

@app.route('/cadastro_materia_prima/', defaults={'id_materia_prima': None}, methods=['GET', 'POST'])
@app.route('/cadastro_materia_prima/<int:id_materia_prima>', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_materia_prima')
def cadastro_materia_prima(id_materia_prima):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            id_mp_form = request.form.get('id_materia_prima')
            codigo = request.form.get('codigo')
            nome = request.form.get('nome')
            descricao = request.form.get('descricao')
            id_unidade = request.form.get('unidade')
            ativo = 1 if 'ativo' in request.form else 0
            
            consumo_diario = request.form.get('consumo_diario', '0').replace(',', '.')
            prazo_entrega = request.form.get('prazo_entrega', '0')
            
            # --- LENDO AS CHECKBOXES RESTAURADAS ---
            permite_estorno = 1 if 'permite_estorno' in request.form else 0
            gera_alerta = 1 if 'gera_alerta' in request.form else 0

            if id_mp_form: # UPDATE
                cursor_local.execute("""
                    UPDATE TBL_MateriaPrima 
                    SET CodigoMateriaPrima = ?, NomeMateriaPrima = ?, Descricao = ?, 
                        IDUnidade = ?, Ativo = ?, PermiteEstorno = ?, GeraAlertaEstoque = ?,
                        ConsumoDiario = ?, PrazoEntregaDias = ?, DataAtualizacao = GETDATE()
                    WHERE IDMateriaPrima = ?
                """, (codigo, nome, descricao, id_unidade, ativo, permite_estorno, gera_alerta, 
                      consumo_diario, prazo_entrega, id_mp_form))
                flash("Matéria-prima atualizada com sucesso!", "success")
            else: # INSERT
                cursor_local.execute("""
                    INSERT INTO TBL_MateriaPrima 
                    (CodigoMateriaPrima, NomeMateriaPrima, Descricao, IDUnidade, Ativo, PermiteEstorno, GeraAlertaEstoque, ConsumoDiario, PrazoEntregaDias)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (codigo, nome, descricao, id_unidade, ativo, permite_estorno, gera_alerta, consumo_diario, prazo_entrega))
                flash("Matéria-prima cadastrada com sucesso!", "success")
            
            conn_local.commit()
            return redirect(url_for('cadastro_materia_prima'))

        # A lógica GET continua igual
        materia_prima_editar = None
        if id_materia_prima:
            cursor_local.execute("SELECT * FROM TBL_MateriaPrima WHERE IDMateriaPrima = ?", id_materia_prima)
            materia_prima_editar = cursor_local.fetchone()
            if not materia_prima_editar:
                flash("Matéria-prima não encontrada.", "error")
                return redirect(url_for('cadastro_materia_prima'))

        cursor_local.execute("SELECT mp.*, um.Sigla FROM TBL_MateriaPrima mp LEFT JOIN TBL_UnidadeMedida um ON mp.IDUnidade = um.IDUnidade ORDER BY mp.NomeMateriaPrima")
        materias_primas = cursor_local.fetchall()
        
        cursor_local.execute("SELECT IDUnidade, Sigla, NomeUnidade FROM TBL_UnidadeMedida ORDER BY NomeUnidade")
        unidades = cursor_local.fetchall()

        return render_template('cadastro_materia_prima.html', 
                               unidades=unidades, 
                               materias_primas=materias_primas,
                               materia_prima_editar=materia_prima_editar)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em cadastro_materia_prima: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar o cadastro de matérias-primas.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            

# #############################################################
# ##### FIM DO NOVO BLOCO - CONTROLE DE ESTOQUE (MATÉRIA-PRIMA) #####
# #############################################################

@app.route('/selecionar_produto_para_estrutura')
@login_requerido
@permissao_requerida('/estrutura_produto') # Reutiliza a permissão principal
def selecionar_produto_para_estrutura():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # Busca todos os produtos habilitados para o usuário selecionar
        cursor_local.execute("""
            SELECT IDProduto, CodigoProduto, NomeProduto 
            FROM TBL_Produto 
            WHERE Habilitado = 1 
            ORDER BY NomeProduto
        """)
        produtos = cursor_local.fetchall()
        
        return render_template('selecionar_produto_para_estrutura.html', produtos=produtos)

    except Exception as e:
        logger.error(f"Erro em selecionar_produto_para_estrutura: {e}", exc_info=True)
        flash("Ocorreu um erro ao carregar a lista de produtos.", "error")
        return redirect(url_for('estoque_dashboard'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
@app.route('/estrutura_produto/<int:id_produto>', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/estrutura_produto')
def cadastro_estrutura_produto(id_produto):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Lógica para ADICIONAR um novo componente
        if request.method == 'POST':
            id_materia_prima = request.form.get('id_materia_prima')
            quantidade = request.form.get('quantidade').replace(',', '.')

            if not id_materia_prima or not quantidade:
                flash("É necessário selecionar uma matéria-prima e informar a quantidade.", "warning")
            else:
                cursor_local.execute("SELECT IDProdutoComponente FROM TBL_ProdutoComponente WHERE IDProduto = ? AND IDMateriaPrima = ?", (id_produto, id_materia_prima))
                if cursor_local.fetchone():
                    flash("Esta matéria-prima já faz parte da estrutura deste produto.", "error")
                else:
                    cursor_local.execute("INSERT INTO TBL_ProdutoComponente (IDProduto, IDMateriaPrima, QuantidadeNecessaria) VALUES (?, ?, ?)", (id_produto, id_materia_prima, quantidade))
                    conn_local.commit()
                    flash("Componente adicionado com sucesso!", "success")
            
            return redirect(url_for('cadastro_estrutura_produto', id_produto=id_produto))

        # Lógica para EXIBIR a página
        cursor_local.execute("SELECT * FROM TBL_Produto WHERE IDProduto = ?", id_produto)
        produto = cursor_local.fetchone()
        if not produto:
            flash("Produto não encontrado.", "error")
            return redirect(url_for('selecionar_produto_para_estrutura'))

        cursor_local.execute("""
            SELECT pc.IDProdutoComponente, mp.NomeMateriaPrima, pc.QuantidadeNecessaria, um.Sigla
            FROM TBL_ProdutoComponente pc
            JOIN TBL_MateriaPrima mp ON pc.IDMateriaPrima = mp.IDMateriaPrima
            LEFT JOIN TBL_UnidadeMedida um ON mp.IDUnidade = um.IDUnidade
            WHERE pc.IDProduto = ? ORDER BY mp.NomeMateriaPrima
        """, id_produto)
        componentes = cursor_local.fetchall()

        cursor_local.execute("SELECT IDMateriaPrima, NomeMateriaPrima FROM TBL_MateriaPrima WHERE Ativo = 1 ORDER BY NomeMateriaPrima")
        materias_primas_disponiveis = cursor_local.fetchall()

        return render_template('cadastro_estrutura_produto.html', 
                               produto=produto, 
                               componentes=componentes,
                               materias_primas_disponiveis=materias_primas_disponiveis)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em cadastro_estrutura_produto: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerenciar a estrutura do produto.", "error")
        return redirect(url_for('selecionar_produto_para_estrutura'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# NOVA ROTA PARA EDITAR A QUANTIDADE DE UM COMPONENTE
@app.route('/estrutura_produto/editar/<int:id_produto_componente>', methods=['POST'])
@login_requerido
@permissao_requerida('/estrutura_produto') # Reutiliza a permissão principal
def editar_componente_estrutura(id_produto_componente):
    conn_local = None
    id_produto = request.form.get('id_produto')
    quantidade = request.form.get('quantidade').replace(',', '.')
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        cursor_local.execute("UPDATE TBL_ProdutoComponente SET QuantidadeNecessaria = ? WHERE IDProdutoComponente = ?", (quantidade, id_produto_componente))
        conn_local.commit()
        flash("Quantidade do componente atualizada com sucesso.", "success")

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao editar componente: {e}", exc_info=True)
        flash("Erro ao editar componente da estrutura.", "error")
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
    return redirect(url_for('cadastro_estrutura_produto', id_produto=id_produto))

# ROTA DE REMOVER CORRIGIDA E MAIS ROBUSTA
@app.route('/estrutura_produto/remover/<int:id_produto_componente>', methods=['POST'])
@login_requerido
@permissao_requerida('/estrutura_produto')
def remover_componente_estrutura(id_produto_componente):
    conn_local = None
    id_produto_para_redirect = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # Primeiro, busca o ID do produto para garantir o redirecionamento correto
        cursor_local.execute("SELECT IDProduto FROM TBL_ProdutoComponente WHERE IDProdutoComponente = ?", (id_produto_componente,))
        componente = cursor_local.fetchone()
        if componente:
            id_produto_para_redirect = componente.IDProduto
        
        # Agora, deleta o componente
        cursor_local.execute("DELETE FROM TBL_ProdutoComponente WHERE IDProdutoComponente = ?", (id_produto_componente,))
        conn_local.commit()
        flash("Componente removido com sucesso.", "success")

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao remover componente: {e}", exc_info=True)
        flash("Erro ao remover componente da estrutura.", "error")
    finally:
        if conn_local:
            devolver_conexao(conn_local)

    if id_produto_para_redirect:
        return redirect(url_for('cadastro_estrutura_produto', id_produto=id_produto_para_redirect))
    else:
        # Fallback caso não encontre o produto
        return redirect(url_for('selecionar_produto_para_estrutura'))


@app.route('/movimentacao_estoque', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/movimentacao_estoque')
def movimentacao_estoque():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        permite_ajuste = obter_configuracao('PERMITE_AJUSTE_ESTOQUE_MANUAL', conn_local, cursor_local) == 'true'

        if request.method == 'POST':
            id_materia_prima = request.form.get('id_materia_prima')
            lote = request.form.get('lote')
            quantidade = request.form.get('quantidade')
            localizacao = request.form.get('localizacao', 'Chão de Fábrica')
            id_usuario = session.get('usuario_id')
            
            id_fornecedor = request.form.get('id_fornecedor')
            numero_nf = request.form.get('numero_nf')
            id_fornecedor = id_fornecedor if id_fornecedor else None

            if not all([id_materia_prima, lote, quantidade]):
                flash("Matéria-Prima, Lote e Quantidade são obrigatórios.", "error")
            else:
                quantidade = quantidade.replace(',', '.') 
                
                cursor_local.execute("""
                    SELECT IDEstoque, QuantidadeDisponivel FROM TBL_EstoqueMP
                    WHERE IDMateriaPrima = ? AND Lote = ? AND Localizacao = ?
                """, (id_materia_prima, lote, localizacao))
                estoque_existente = cursor_local.fetchone()

                if estoque_existente:
                    nova_quantidade = estoque_existente.QuantidadeDisponivel + float(quantidade)
                    cursor_local.execute("UPDATE TBL_EstoqueMP SET QuantidadeDisponivel = ? WHERE IDEstoque = ?", (nova_quantidade, estoque_existente.IDEstoque))
                    id_estoque_mp = estoque_existente.IDEstoque
                else:
                    cursor_local.execute("""
                        INSERT INTO TBL_EstoqueMP (IDMateriaPrima, Lote, QuantidadeDisponivel, Localizacao, IDFornecedor, NumeroNotaFiscal)
                        OUTPUT INSERTED.IDEstoque
                        VALUES (?, ?, ?, ?, ?, ?)
                    """, (id_materia_prima, lote, quantidade, localizacao, id_fornecedor, numero_nf))
                    id_estoque_mp = cursor_local.fetchone()[0]
                
                cursor_local.execute("""
                    INSERT INTO TBL_LogMovimentacaoEstoque (IDEstoqueMP, IDMateriaPrima, Lote, TipoMovimento, Quantidade, IDUsuario, Observacao, IDFornecedor, NumeroNotaFiscal)
                    VALUES (?, ?, ?, 'ENTRADA_MANUAL', ?, ?, 'Entrada manual de lote', ?, ?)
                """, (id_estoque_mp, id_materia_prima, lote, quantidade, id_usuario, id_fornecedor, numero_nf))

                cursor_local.execute("UPDATE TBL_MateriaPrima SET AlertaCompraEnviado = 0 WHERE IDMateriaPrima = ?", (id_materia_prima,))
                
                conn_local.commit()
                flash("Entrada de estoque registada com sucesso!", "success")
            
            return redirect(url_for('movimentacao_estoque'))

        cursor_local.execute("""
            SELECT E.IDEstoque, MP.IDMateriaPrima, MP.NomeMateriaPrima, E.Lote, E.QuantidadeDisponivel, 
                   E.Localizacao, UM.Sigla, F.NomeFantasia AS NomeFornecedor, E.NumeroNotaFiscal
            FROM TBL_EstoqueMP E
            JOIN TBL_MateriaPrima MP ON E.IDMateriaPrima = MP.IDMateriaPrima
            LEFT JOIN TBL_UnidadeMedida UM ON MP.IDUnidade = UM.IDUnidade
            LEFT JOIN TBL_Fornecedor F ON E.IDFornecedor = F.IDFornecedor
            WHERE E.QuantidadeDisponivel > 0
            ORDER BY MP.NomeMateriaPrima, E.Lote
        """)
        estoque_atual = cursor_local.fetchall()

        cursor_local.execute("SELECT IDMateriaPrima, NomeMateriaPrima FROM TBL_MateriaPrima WHERE Ativo = 1 ORDER BY NomeMateriaPrima")
        materias_primas = cursor_local.fetchall()
        
        cursor_local.execute("SELECT IDFornecedor, NomeFantasia FROM TBL_Fornecedor WHERE Ativo = 1 ORDER BY NomeFantasia")
        fornecedores = cursor_local.fetchall()

        return render_template('movimentacao_estoque.html',
                               materias_primas=materias_primas,
                               fornecedores=fornecedores,
                               estoque_atual=estoque_atual,
                               permite_ajuste=permite_ajuste)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em movimentacao_estoque: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar a movimentação de estoque.", "error")
        return redirect(url_for('estoque_dashboard'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/consulta_estoque')
@login_requerido
@permissao_requerida('/consulta_estoque')
def consulta_estoque():
    conn_local = None
    tipo_estoque = request.args.get('tipo', 'mp')
    
    # Captura todos os filtros da URL, incluindo os novos de data
    filtros = {
        "id_item": request.args.get("id_item", ""),
        "lote": request.args.get("lote", ""),
        "localizacao": request.args.get("localizacao", ""),
        "data_inicio": request.args.get("data_inicio", ""), # NOVO
        "data_fim": request.args.get("data_fim", "")        # NOVO
    }
    
    resultados = []
    itens_filtro = []
    
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        params = []
        if tipo_estoque == 'mp':
            query = """
                SELECT E.IDEstoque AS ID, MP.NomeMateriaPrima AS NomeItem, E.Lote, E.QuantidadeDisponivel, E.Localizacao, UM.Sigla, E.DataEntrada
                FROM TBL_EstoqueMP E
                JOIN TBL_MateriaPrima MP ON E.IDMateriaPrima = MP.IDMateriaPrima
                LEFT JOIN TBL_UnidadeMedida UM ON MP.IDUnidade = UM.IDUnidade
                WHERE 1=1
            """
            if filtros["id_item"]:
                query += " AND E.IDMateriaPrima = ?"
                params.append(filtros["id_item"])
            
            cursor_local.execute("SELECT IDMateriaPrima AS ID, NomeMateriaPrima AS Nome FROM TBL_MateriaPrima WHERE Ativo = 1 ORDER BY Nome")
            itens_filtro = cursor_local.fetchall()

        elif tipo_estoque == 'pa':
            query = """
                SELECT E.IDEstoquePA AS ID, P.NomeProduto AS NomeItem, E.Lote, E.QuantidadeDisponivel, E.Localizacao, UM.Sigla, E.DataEntrada
                FROM TBL_EstoqueProdutoAcabado E
                JOIN TBL_Produto P ON E.IDProduto = P.IDProduto
                LEFT JOIN TBL_UnidadeMedida UM ON P.IDUnidade = UM.IDUnidade
                WHERE 1=1
            """
            if filtros["id_item"]:
                query += " AND E.IDProduto = ?"
                params.append(filtros["id_item"])
            
            cursor_local.execute("SELECT IDProduto AS ID, NomeProduto AS Nome FROM TBL_Produto WHERE Habilitado = 1 ORDER BY Nome")
            itens_filtro = cursor_local.fetchall()

        if filtros["lote"]:
            query += " AND E.Lote LIKE ?"
            params.append(f"%{filtros['lote']}%")
        if filtros["localizacao"]:
            query += " AND E.Localizacao LIKE ?"
            params.append(f"%{filtros['localizacao']}%")

        # --- LÓGICA ADICIONADA PARA O FILTRO DE DATA ---
        if filtros["data_inicio"]:
            query += " AND CAST(E.DataEntrada AS DATE) >= ?"
            params.append(filtros["data_inicio"])
        if filtros["data_fim"]:
            query += " AND CAST(E.DataEntrada AS DATE) <= ?"
            params.append(filtros["data_fim"])
        # --- FIM DA ADIÇÃO ---
        
        query += " ORDER BY NomeItem, E.DataEntrada DESC"
        
        cursor_local.execute(query, params)
        resultados = cursor_local.fetchall()

        return render_template('consulta_estoque.html',
                               resultados=resultados,
                               itens_filtro=itens_filtro,
                               filtros=filtros,
                               tipo_estoque=tipo_estoque)

    except Exception as e:
        logger.error(f"Erro em consulta_estoque: {e}", exc_info=True)
        flash("Ocorreu um erro ao consultar o estoque.", "error")
        return redirect(url_for('estoque_dashboard'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
# FUNÇÃO AUXILIAR (VERSÃO CORRETA - USA SET COM BASE NO TOTAL DA ÚLTIMA OP)
def _adicionar_produto_acabado_ao_estoque(cursor_local, id_ordem, id_produto, quantidade_total_liquida_ultima_op):
    """
    Adiciona ou AJUSTA a quantidade produzida de um PA no estoque.
    Usa o código da OP como lote. Se já existir, DEFINE a quantidade para o total da última op.
    Recebe a QUANTIDADE TOTAL LÍQUIDA CALCULADA PARA A ÚLTIMA OPERAÇÃO.
    VERSÃO COM LOGS DETALHADOS e conversão float.
    """
    try:
        # Renomeando parâmetro para clareza
        quantidade_total_ultima_op_float = float(quantidade_total_liquida_ultima_op or 0.0)

        logger.info(f"[Estoque PA - SET - INÍCIO] Ordem ID: {id_ordem}, Produto ID: {id_produto}, Qtd Total Líquida (Última Op) Recebida: {quantidade_total_ultima_op_float}")

        cursor_local.execute("SELECT CodigoOrdem FROM TBL_OrdemProducao WHERE IDOrdem = ?", id_ordem)
        ordem_info = cursor_local.fetchone()
        lote_pa = ordem_info.CodigoOrdem if ordem_info else f"LOTE-OP-{id_ordem}"
        logger.debug(f"[Estoque PA - SET] Lote PA determinado: {lote_pa}")

        cursor_local.execute("""
            SELECT IDEstoquePA, QuantidadeDisponivel
            FROM TBL_EstoqueProdutoAcabado
            WHERE IDProduto = ? AND Lote = ?
        """, (id_produto, lote_pa))
        estoque_pa_existente = cursor_local.fetchone()

        quantidade_a_registrar_no_log = 0.0
        tipo_movimento_log = 'ENTRADA_PRODUCAO'
        obs_log = f"Entrada por finalização da OP {lote_pa}"
        id_estoque_pa_log = None

        if estoque_pa_existente:
            id_estoque_pa_log = estoque_pa_existente.IDEstoquePA
            quantidade_atual_estoque = float(estoque_pa_existente.QuantidadeDisponivel or 0.0)
            logger.info(f"[Estoque PA - SET] Lote EXISTENTE encontrado (ID: {id_estoque_pa_log}). Saldo ATUAL no DB: {quantidade_atual_estoque}")

            # Calcula a DIFERENÇA apenas para o log
            quantidade_a_registrar_no_log = quantidade_total_ultima_op_float - quantidade_atual_estoque
            tipo_movimento_log = 'AJUSTE_PRODUCAO'
            obs_log = f"Ajuste por re-finalização da OP {lote_pa}. Saldo anterior: {quantidade_atual_estoque:.4f}, Saldo final DEVERIA SER: {quantidade_total_ultima_op_float:.4f}"
            logger.debug(f"[Estoque PA - SET] Calculado ajuste para o log: {quantidade_a_registrar_no_log:.4f}")

            # *** PONTO CRÍTICO - O UPDATE USA SET ***
            logger.info(f"[Estoque PA - SET] Executando UPDATE: SET QuantidadeDisponivel = {quantidade_total_ultima_op_float} WHERE IDEstoquePA = {id_estoque_pa_log}")
            cursor_local.execute("""
                UPDATE TBL_EstoqueProdutoAcabado SET QuantidadeDisponivel = ?
                WHERE IDEstoquePA = ?
            """, (quantidade_total_ultima_op_float, estoque_pa_existente.IDEstoquePA))
            logger.info(f"[Estoque PA - SET] UPDATE executado. Saldo DEVERIA ser {quantidade_total_ultima_op_float:.4f}")

        else:
            logger.info(f"[Estoque PA - SET] Lote NÃO encontrado. Criando novo registro.")
            quantidade_a_registrar_no_log = quantidade_total_ultima_op_float # Log reflete a entrada inicial
            logger.info(f"[Estoque PA - SET] Executando INSERT: Lote={lote_pa}, QuantidadeDisponivel = {quantidade_total_ultima_op_float}")
            cursor_local.execute("""
                INSERT INTO TBL_EstoqueProdutoAcabado (IDProduto, Lote, QuantidadeDisponivel)
                OUTPUT INSERTED.IDEstoquePA
                VALUES (?, ?, ?)
            """, (id_produto, lote_pa, quantidade_total_ultima_op_float))
            id_estoque_pa_log = cursor_local.fetchone()[0]
            logger.info(f"[Estoque PA - SET] INSERT executado. Novo IDEstoquePA: {id_estoque_pa_log}")
            obs_log = f"Entrada inicial por finalização da OP {lote_pa}"


        if abs(quantidade_a_registrar_no_log) > 0.001:
             logger.debug(f"[Estoque PA - SET] Registrando LogMovimentacao: Tipo={tipo_movimento_log}, Qtd={quantidade_a_registrar_no_log:.4f}")
             cursor_local.execute("""
                 INSERT INTO TBL_LogMovimentacaoEstoque
                 (IDEstoquePA, IDProduto, Lote, TipoMovimento, Quantidade, Observacao)
                 VALUES (?, ?, ?, ?, ?, ?)
             """, (id_estoque_pa_log, id_produto, lote_pa, tipo_movimento_log, quantidade_a_registrar_no_log, obs_log))
        else:
             logger.info("[Estoque PA - SET] Ajuste calculado para o log é zero. Log de movimentação não será criado.")

        logger.info(f"[Estoque PA - SET - FIM] Processamento concluído para Ordem ID: {id_ordem}")

    except Exception as e:
        logger.error(f"[Estoque PA - SET - ERRO] Falha ao processar estoque para Ordem ID {id_ordem}: {e}", exc_info=True)
        raise
def _estornar_componentes_para_estoque(cursor_local, id_execucao, id_produto, quantidade_estornada):
    """
    Função auxiliar para DEVOLVER matérias-primas ao estoque do chão de fábrica.
    Respeita a flag 'PermiteEstorno' de cada matéria-prima.
    """
    try:
        # Busca a "receita" (BOM) do produto que foi fabricado
        cursor_local.execute("""
            SELECT PC.IDMateriaPrima, PC.QuantidadeNecessaria, MP.PermiteEstorno, MP.NomeMateriaPrima
            FROM TBL_ProdutoComponente PC
            JOIN TBL_MateriaPrima MP ON PC.IDMateriaPrima = MP.IDMateriaPrima
            WHERE PC.IDProduto = ?
        """, (id_produto,))
        componentes = cursor_local.fetchall()

        for componente in componentes:
            # SÓ DEVOLVE AO ESTOQUE SE O MATERIAL PERMITIR
            if not componente.PermiteEstorno:
                logger.info(f"Estorno pulado para o componente '{componente.NomeMateriaPrima}' (ID: {componente.IDMateriaPrima}) pois ele não é estornável.")
                continue # Pula para o próximo componente

            quantidade_a_devolver = float(componente.QuantidadeNecessaria) * quantidade_estornada
            
            # Precisamos encontrar o log de consumo original para saber de qual lote devolver
            # Esta é uma abordagem simplificada, assumindo que o último consumo foi o deste evento
            cursor_local.execute("""
                SELECT TOP 1 IDEstoqueMP, Lote FROM TBL_LogMovimentacaoEstoque
                WHERE IDExecucaoOP = ? AND IDMateriaPrima = ? AND TipoMovimento = 'CONSUMO_PRODUCAO'
                ORDER BY Timestamp DESC
            """, (id_execucao, componente.IDMateriaPrima))
            log_consumo = cursor_local.fetchone()

            if not log_consumo:
                logger.warning(f"Não foi possível encontrar o log de consumo original para a Matéria-Prima ID {componente.IDMateriaPrima} na execução {id_execucao}. O estoque não foi devolvido.")
                continue

            # Adiciona a quantidade de volta ao lote de origem
            cursor_local.execute("""
                UPDATE TBL_EstoqueMP SET QuantidadeDisponivel = QuantidadeDisponivel + ?
                WHERE IDEstoque = ?
            """, (quantidade_a_devolver, log_consumo.IDEstoqueMP))

            # Registra o estorno no log de movimentação
            cursor_local.execute("""
                INSERT INTO TBL_LogMovimentacaoEstoque (IDEstoqueMP, IDMateriaPrima, Lote, TipoMovimento, Quantidade, IDExecucaoOP, Observacao)
                VALUES (?, ?, ?, 'ESTORNO_CONSUMO', ?, ?, ?)
            """, (log_consumo.IDEstoqueMP, componente.IDMateriaPrima, log_consumo.Lote, quantidade_a_devolver, id_execucao, f"Estorno de produção"))
            
            logger.info(f"Estornado {quantidade_a_devolver} do Lote {log_consumo.Lote} da Matéria-Prima ID {componente.IDMateriaPrima} para o estoque.")

        return True
    
    except Exception as e:
        logger.error(f"Erro na função _estornar_componentes_para_estoque: {e}", exc_info=True)
        raise

# Em planner_app.py, substitua novamente esta função:

@app.route('/producao/estornar_ultima/<int:id_maquina>', methods=['POST'])
@login_requerido
@permissao_requerida('/dashboard')
def estornar_ultima_producao(id_maquina):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        data = request.get_json()
        if not data:
            return jsonify({'success': False, 'message': 'Dados da requisição inválidos.'}), 400

        tipo_estorno = data.get('tipo_estorno')
        quantidade_str = data.get('quantidade_estorno')
        motivo_estorno = data.get('motivo_estorno', 'Estorno manual pelo operador')
        devolver_mp = data.get('devolver_mp', False)

        if not quantidade_str:
            return jsonify({'success': False, 'message': 'Quantidade para estorno não foi fornecida.'}), 400
            
        quantidade_a_estornar = float(str(quantidade_str).replace(',', '.'))
        
        cursor_local.execute("SELECT TOP 1 E.IDExecucao, O.IDProduto, E.IDOrdem, E.IDOperador, E.IDTurno, R.IDTipo AS IDTipoRecurso FROM TBL_ExecucaoOP E JOIN TBL_OrdemProducao O ON E.IDOrdem = O.IDOrdem JOIN TBL_Recurso R ON E.IDMaquina = R.IDMaquina WHERE E.IDMaquina = ? AND E.Status = 'Em Execucao' ORDER BY E.DataHoraInicio DESC", (id_maquina,))
        execucao_ativa = cursor_local.fetchone()
        
        if not execucao_ativa:
            return jsonify({'success': False, 'message': 'Nenhuma ordem de produção ativa encontrada para esta máquina.'}), 404

        # --- MUDANÇA NA CONSULTA DE VALIDAÇÃO ---
        # Agora verifica o saldo líquido da ORDEM DE PRODUÇÃO inteira.
        cursor_local.execute("""
            SELECT SUM(Quantidade) as TotalProduzidoNet 
            FROM VW_EventoProducaoComCicloReal 
            WHERE IDOrdemProducao = ? AND TipoValor IN ('BOA', 'ESTORNO')
        """, (execucao_ativa.IDOrdem,)) # Usa IDOrdem em vez de IDExecucao
        producao = cursor_local.fetchone()
        total_produzido_liquido = float(producao.TotalProduzidoNet or 0)

        if quantidade_a_estornar <= 0:
            return jsonify({'success': False, 'message': 'A quantidade a ser estornada deve ser maior que zero.'}), 400

        if quantidade_a_estornar > total_produzido_liquido:
            msg = f"Erro: A quantidade a estornar ({quantidade_a_estornar}) não pode ser maior que o saldo líquido produzido na ORDEM INTEIRA ({total_produzido_liquido})."
            return jsonify({'success': False, 'message': msg}), 400
        
        # O resto da função permanece igual...
        obs_final = f"Estorno de {quantidade_a_estornar} un. Motivo: {motivo_estorno}"
        
        cursor_local.execute("""
            INSERT INTO VW_EventoProducaoComCicloReal (IDExecucao, IDOrdemProducao, IDMaquina, IDOperador, IDTurno, IDTipoRecurso,
            Quantidade, TipoValor, OrigemEvento, ObsEvento, DataHoraEvento, IDTipoEvento)
            VALUES (?, ?, ?, ?, ?, ?, ?, 'ESTORNO', 'MANUAL', ?, GETDATE(), 2)
        """, (
            execucao_ativa.IDExecucao, execucao_ativa.IDOrdem, id_maquina, session.get('usuario_id'),
            execucao_ativa.IDTurno, execucao_ativa.IDTipoRecurso, 
            -quantidade_a_estornar,
            obs_final
        ))
        
        if tipo_estorno == 'reclassificar_refugo':
            cursor_local.execute("""
                INSERT INTO VW_EventoProducaoComCicloReal (IDExecucao, IDOrdemProducao, IDMaquina, IDOperador, IDTurno, IDTipoRecurso,
                Quantidade, TipoValor, OrigemEvento, ObsEvento, DataHoraEvento, IDTipoEvento)
                VALUES (?, ?, ?, ?, ?, ?, ?, 'REFUGO', 'MANUAL_ESTORNO', ?, GETDATE(), 2)
            """, (
                execucao_ativa.IDExecucao, execucao_ativa.IDOrdem, id_maquina, session.get('usuario_id'),
                execucao_ativa.IDTurno, execucao_ativa.IDTipoRecurso, 
                quantidade_a_estornar,
                f"Reclassificado via estorno. Motivo: {motivo_estorno}"
            ))
            logger.info(f"{quantidade_a_estornar} unidades reclassificadas como refugo.")
            
        elif tipo_estorno == 'correcao' and devolver_mp:
            _estornar_componentes_para_estoque(cursor_local, execucao_ativa.IDExecucao, execucao_ativa.IDProduto, quantidade_a_estornar)

        conn_local.commit()
        return jsonify({'success': True, 'message': 'Produção estornada com sucesso!'})

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao estornar produção: {e}", exc_info=True)
        return jsonify({'success': False, 'message': f'Ocorreu um erro inesperado no servidor: {str(e)}'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/api/verificar_estoque_op/<int:id_ordem>')
@login_requerido
def api_verificar_estoque_op(id_ordem):
    """
    Endpoint da API para ser chamado pelo JavaScript do front-end.
    """
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        resultado = _verificar_estoque_para_op(cursor_local, id_ordem)
        return jsonify(resultado)
    except Exception as e:
        logger.error(f"Erro na rota /api/verificar_estoque_op: {e}", exc_info=True)
        return jsonify({'status': 'error', 'message': 'Erro de servidor.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
def _verificar_estoque_para_op(cursor_local, id_ordem):
    """
    VERSÃO FINAL: O alerta de ressuprimento é enviado silenciosamente por e-mail,
    e a função retorna 'success' se houver estoque para a OP, não bloqueando o operador.
    """
    try:
        cursor_local.execute("""
            SELECT IDProduto, QuantidadePlanejada
            FROM TBL_OrdemProducao WHERE IDOrdem = ?
        """, id_ordem)
        ordem_info = cursor_local.fetchone()

        if not ordem_info or not ordem_info.QuantidadePlanejada:
            return {'status': 'success', 'message': 'Ordem sem quantidade planejada, verificação de estoque não aplicável.'}

        id_produto = ordem_info.IDProduto
        quantidade_planejada = float(ordem_info.QuantidadePlanejada)

        cursor_local.execute("""
            SELECT
                PC.IDMateriaPrima, PC.QuantidadeNecessaria, MP.NomeMateriaPrima, UM.Sigla,
                MP.ConsumoDiario, MP.PrazoEntregaDias, MP.AlertaCompraEnviado
            FROM TBL_ProdutoComponente PC
            JOIN TBL_MateriaPrima MP ON PC.IDMateriaPrima = MP.IDMateriaPrima
            LEFT JOIN TBL_UnidadeMedida UM ON MP.IDUnidade = UM.IDUnidade
            WHERE PC.IDProduto = ?
        """, id_produto)
        componentes = cursor_local.fetchall()

        if not componentes:
            return {'status': 'success', 'message': 'Produto sem estrutura definida.'}

        cursor_local.execute("""
            SELECT IDMateriaPrima, SUM(ISNULL(QuantidadeDisponivel, 0)) as Saldo
            FROM TBL_EstoqueMP GROUP BY IDMateriaPrima
        """)
        estoque_atual = {row.IDMateriaPrima: float(row.Saldo) for row in cursor_local.fetchall()}

        faltas = []

        for componente in componentes:
            id_mp = componente.IDMateriaPrima
            quantidade_necessaria_total = float(componente.QuantidadeNecessaria) * quantidade_planejada
            saldo_disponivel = estoque_atual.get(id_mp, 0.0)

            # Lógica de Alerta de Compra (Ressuprimento) - executada em segundo plano
            if componente.ConsumoDiario and componente.PrazoEntregaDias and not componente.AlertaCompraEnviado:
                consumo_diario = float(componente.ConsumoDiario)
                prazo_entrega = int(componente.PrazoEntregaDias)

                if consumo_diario > 0 and prazo_entrega > 0:
                    estoque_seguranca = (consumo_diario * prazo_entrega) * 0.20
                    ponto_ressuprimento = (consumo_diario * prazo_entrega) + estoque_seguranca

                    if saldo_disponivel <= ponto_ressuprimento:
                        logger.warning(f"ALERTA PREVENTIVO via E-MAIL: Estoque de '{componente.NomeMateriaPrima}' ({saldo_disponivel}) está abaixo do ponto de ressuprimento ({ponto_ressuprimento}).")

                        enviar_email_alerta_compra_mp(
                            nome_materia_prima=componente.NomeMateriaPrima,
                            saldo_atual=saldo_disponivel,
                            ponto_ressuprimento=ponto_ressuprimento,
                            consumo_diario=consumo_diario,
                            prazo_entrega=prazo_entrega
                        )

                        cursor_local.execute("UPDATE TBL_MateriaPrima SET AlertaCompraEnviado = 1 WHERE IDMateriaPrima = ?", (id_mp,))

            # Lógica de Falta de Estoque para a Ordem (bloqueia o usuário)
            if saldo_disponivel < quantidade_necessaria_total:
                faltas.append({
                    'nome_mp': componente.NomeMateriaPrima,
                    'necessario': f"{quantidade_necessaria_total:,.2f}".replace(",", "X").replace(".", ",").replace("X", "."),
                    'disponivel': f"{saldo_disponivel:,.2f}".replace(",", "X").replace(".", ",").replace("X", "."),
                    'unidade': componente.Sigla
                })

        # --- INÍCIO DA ALTERAÇÃO NO RETORNO ---
        # Se houver falta de estoque para a OP, retorna um aviso para o usuário decidir.
        if faltas:
            return {'status': 'warning', 'faltas': faltas}
        else:
            # Se não houver falta de estoque, SEMPRE retorna sucesso.
            # O e-mail de alerta de ressuprimento (se necessário) já foi enviado em segundo plano.
            return {'status': 'success'}
        # --- FIM DA ALTERAÇÃO NO RETORNO ---

    except Exception as e:
        logger.error(f"Erro em _verificar_estoque_para_op: {e}", exc_info=True)
        return {'status': 'error', 'message': 'Erro interno ao verificar o estoque.'}
        
def _consumir_estoque_para_ordem(cursor_local, id_ordem, id_execucao):
    """
    Função auxiliar para consolidar e consumir o estoque de uma ordem inteira.
    VERSÃO CORRIGIDA: Verifica o que já foi consumido para evitar duplicidade.
    """
    try:
        # Pega o ID do Produto a partir da Ordem
        cursor_local.execute("SELECT IDProduto FROM TBL_OrdemProducao WHERE IDOrdem = ?", (id_ordem,))
        produto_row = cursor_local.fetchone()
        if not produto_row:
            raise Exception(f"Produto não encontrado para a Ordem ID {id_ordem}")
        id_produto = produto_row.IDProduto

        # 1. Calcula o total produzido LÍQUIDO nesta execução (peças boas - estornos)
        cursor_local.execute("""
            SELECT SUM(Quantidade) as TotalProduzidoLiquido
            FROM VW_EventoProducaoComCicloReal WITH (NOLOCK)
            WHERE IDExecucao = ? AND TipoValor IN ('BOA', 'ESTORNO')
        """, (id_execucao,))
        total_produzido_row = cursor_local.fetchone()
        total_produzido_liquido = total_produzido_row.TotalProduzidoLiquido if total_produzido_row and total_produzido_row.TotalProduzidoLiquido is not None else 0

        # 2. Verifica na tabela de log o quanto de material já foi consumido para esta execução
        cursor_local.execute("""
            SELECT SUM(PC.QuantidadeNecessaria * (ABS(L.Quantidade) / P.FatorMultiplicacao)) 
            FROM TBL_LogMovimentacaoEstoque L
            JOIN TBL_ExecucaoOP EX ON L.IDExecucaoOP = EX.IDExecucao
            JOIN TBL_OrdemProducao OP ON EX.IDOrdem = OP.IDOrdem
            JOIN TBL_Produto P ON OP.IDProduto = P.IDProduto
            JOIN TBL_ProdutoComponente PC ON P.IDProduto = PC.IDProduto AND L.IDMateriaPrima = PC.IDMateriaPrima
            WHERE L.IDExecucaoOP = ? AND L.TipoMovimento = 'CONSUMO_PRODUCAO'
        """, (id_execucao,))
        
        # Este cálculo é uma estimativa. Uma forma mais simples e direta é calcular com base nas peças.
        cursor_local.execute("""
            SELECT SUM(ABS(Quantidade)) 
            FROM TBL_LogMovimentacaoEstoque 
            WHERE IDExecucaoOP = ? AND TipoMovimento = 'CONSUMO_PRODUCAO'
        """, (id_execucao,))
        # Esta abordagem é complexa. Vamos simplificar: vamos rastrear as peças.
        
        cursor_local.execute("""
            SELECT SUM(QuantidadeConsumida) 
            FROM TBL_ExecucaoOP_ConsumoLog 
            WHERE IDExecucao = ?
        """, (id_execucao,))
        consumo_log_row = cursor_local.fetchone()
        total_pecas_ja_consumidas = consumo_log_row[0] if consumo_log_row and consumo_log_row[0] is not None else 0

        # 3. Calcula a diferença que realmente precisa ser consumida agora
        quantidade_a_consumir = total_produzido_liquido - total_pecas_ja_consumidas

        logger.info(f"Consumo de estoque para Execução ID {id_execucao}: Total produzido: {total_produzido_liquido}, Já consumido para: {total_pecas_ja_consumidas}, Consumindo agora para: {quantidade_a_consumir} unidades.")
        
        if quantidade_a_consumir > 0:
            # Chama a função de consumo, agora passando a quantidade correta
            _consumir_componentes_por_producao(
                cursor_local=cursor_local,
                id_execucao=id_execucao,
                id_produto=id_produto,
                quantidade_produzida=float(quantidade_a_consumir),
                id_ordem_producao=id_ordem
            )
            
            # 4. Registra no novo log de controle que consumimos para esta quantidade
            cursor_local.execute("""
                INSERT INTO TBL_ExecucaoOP_ConsumoLog (IDExecucao, QuantidadeConsumida)
                VALUES (?, ?)
            """, (id_execucao, quantidade_a_consumir))

        return True

    except Exception as e:
        logger.error(f"Falha CRÍTICA ao consumir estoque para a Ordem ID {id_ordem}: {e}", exc_info=True)
        raise

@app.route('/editar_estoque_manual', methods=['POST'])
@login_requerido
@permissao_requerida('/movimentacao_estoque')
def editar_estoque_manual():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        permite_ajuste = obter_configuracao('PERMITE_AJUSTE_ESTOQUE_MANUAL', conn_local, cursor_local) == 'true'
        if not permite_ajuste:
            flash("O ajuste manual de estoque está desabilitado nas configurações.", "error")
            return redirect(url_for('movimentacao_estoque'))

        id_estoque = request.form.get('id_estoque')
        nova_quantidade_str = request.form.get('quantidade').replace(',', '.')
        id_usuario = session.get('usuario_id')

        cursor_local.execute("""
            SELECT E.QuantidadeDisponivel, E.IDMateriaPrima, E.Lote, MP.NomeMateriaPrima
            FROM TBL_EstoqueMP E
            JOIN TBL_MateriaPrima MP ON E.IDMateriaPrima = MP.IDMateriaPrima
            WHERE E.IDEstoque = ?
        """, id_estoque)
        estoque_antigo = cursor_local.fetchone()
        
        if not estoque_antigo:
            flash("Item de estoque não encontrado para edição.", "error")
            return redirect(url_for('movimentacao_estoque'))

        quantidade_antiga = float(estoque_antigo.QuantidadeDisponivel)
        nova_quantidade = float(nova_quantidade_str)
        diferenca = nova_quantidade - quantidade_antiga

        cursor_local.execute(
            "UPDATE TBL_EstoqueMP SET QuantidadeDisponivel = ? WHERE IDEstoque = ?",
            (nova_quantidade, id_estoque)
        )

        qtd_antiga_fmt = ("%g" % quantidade_antiga).replace('.', ',')
        nova_qtd_fmt = ("%g" % nova_quantidade).replace('.', ',')
        obs = f"Ajuste manual de '{estoque_antigo.NomeMateriaPrima}'. De: {qtd_antiga_fmt} Para: {nova_qtd_fmt}"
        
        cursor_local.execute("""
            INSERT INTO TBL_LogMovimentacaoEstoque 
            (IDEstoqueMP, IDMateriaPrima, Lote, TipoMovimento, Quantidade, IDUsuario, Observacao)
            VALUES (?, ?, ?, 'AJUSTE_MANUAL', ?, ?, ?)
        """, (id_estoque, estoque_antigo.IDMateriaPrima, estoque_antigo.Lote, diferenca, id_usuario, obs))

        conn_local.commit()
        flash("Estoque atualizado com sucesso!", "success")

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em editar_estoque_manual: {e}", exc_info=True)
        flash("Ocorreu um erro ao editar o estoque.", "error")
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
    return redirect(url_for('movimentacao_estoque'))
    
@app.route('/api/maquina/<int:id_maquina>/eventos_recentes')
@login_requerido
def api_eventos_recentes_maquina(id_maquina):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # CORREÇÃO: Trocado 'IDEventoProducao' por 'IDEvento'
        cursor_local.execute("""
            SELECT TOP 10
                IDEvento, 
                Quantidade,
                DataHoraEvento
            FROM VW_EventoProducaoComCicloReal
            WHERE IDMaquina = ? AND TipoValor = 'BOA'
            ORDER BY DataHoraEvento DESC
        """, (id_maquina,))
        
        eventos = []
        for row in cursor_local.fetchall():
            eventos.append({
                # CORREÇÃO: Trocado 'row.IDEventoProducao' por 'row.IDEvento'
                'id_evento': row.IDEvento,
                'quantidade': ("%g" % float(row.Quantidade)).replace('.', ','),
                'data_hora': row.DataHoraEvento.strftime('%d/%m/%Y %H:%M:%S')
            })
            
        return jsonify(eventos)

    except Exception as e:
        logger.error(f"Erro em api_eventos_recentes_maquina: {e}", exc_info=True)
        return jsonify({"erro": "Não foi possível buscar os eventos"}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
@app.route('/api/maquina/<int:id_maquina>/info_producao_ativa')
@login_requerido
def api_info_producao_ativa(id_maquina):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # Primeiro, encontra a execução ativa para a máquina
        cursor_local.execute("""
            SELECT TOP 1 IDExecucao 
            FROM TBL_ExecucaoOP 
            WHERE IDMaquina = ? AND Status = 'Em Execucao'
        """, (id_maquina,))
        execucao = cursor_local.fetchone()
        
        if not execucao:
            return jsonify({'total_produzido': 0})

        # Agora, soma toda a produção 'BOA' para essa execução
        cursor_local.execute("""
            SELECT SUM(Quantidade) as TotalProduzido 
            FROM VW_EventoProducaoComCicloReal 
            WHERE IDExecucao = ? AND TipoValor = 'BOA'
        """, (execucao.IDExecucao,))
        producao = cursor_local.fetchone()
        
        total_produzido = float(producao.TotalProduzido or 0)
            
        return jsonify({'total_produzido': total_produzido})

    except Exception as e:
        logger.error(f"Erro em api_info_producao_ativa: {e}", exc_info=True)
        return jsonify({"erro": "Não foi possível buscar a produção total"}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local) 
            
# Em planner_app.py, SUBSTITUA a função da linha 7291:

@app.route('/documento_tecnico/<path:filename>')
@login_requerido
def servir_documento_tecnico(filename):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # #############################################
        # ##          INÍCIO DA ALTERAÇÃO           ##
        # #############################################
        
        # Pega o '?tipo=' da URL (ex: ?tipo=operacao)
        tipo_documento = request.args.get('tipo', 'produto') # 'produto' é o padrão
        
        caminho_base_produto = obter_configuracao('CAMINHO_BASE_DOCUMENTOS', conn_local, cursor_local)
        caminho_base_operacao = obter_configuracao('CAMINHO_BASE_DOCUMENTOS_OPERACAO', conn_local, cursor_local)

        caminho_base = None
        
        # Se o tipo for 'operacao' E um caminho específico para operação foi definido...
        if tipo_documento == 'operacao' and caminho_base_operacao:
            caminho_base = caminho_base_operacao
            logger.info(f"Servindo documento de OPERAÇÃO: {filename} de {caminho_base}")
        else:
            # Para 'produto' ou se o caminho da operação estiver vazio, usa o caminho padrão
            caminho_base = caminho_base_produto
            logger.info(f"Servindo documento de PRODUTO (ou fallback): {filename} de {caminho_base}")

        # #############################################
        # ##           FIM DA ALTERAÇÃO            ##
        # #############################################

        if not caminho_base:
            logger.error("A configuração 'CAMINHO_BASE_DOCUMENTOS' (caminho principal) não foi definida no sistema.")
            flash("Erro de configuração: O caminho base para documentos técnicos não foi definido.", "error")
            return redirect(request.referrer or url_for('dashboard'))
    
        if not os.path.isdir(caminho_base):
            logger.error(f"O diretório configurado '{caminho_base}' não existe ou não é um diretório válido no servidor.")
            flash(f"Erro de servidor: O diretório de documentos '{caminho_base}' é inválido.", "error")
            return redirect(request.referrer or url_for('dashboard'))

        possible_filenames = [
            filename,          
            f"{filename}.pdf",  
            f"{filename}.PDF"   
        ]

        for name_to_try in possible_filenames:
            full_path = os.path.join(caminho_base, name_to_try)
            if os.path.exists(full_path):
                logger.info(f"Documento encontrado: '{full_path}'. Servindo o arquivo.")
                return send_from_directory(directory=caminho_base, path=name_to_try, as_attachment=False)

        logger.warning(f"Documento não encontrado para '{filename}' em '{caminho_base}' (verificadas extensões comuns)")
        flash(f"O documento '{filename}' não foi encontrado no servidor.", "error")
        return redirect(request.referrer or url_for('dashboard'))

    except Exception as e:
        logger.error(f"Erro ao servir documento técnico '{filename}': {e}", exc_info=True)
        flash("Ocorreu um erro interno ao tentar acessar o documento.", "error")
        return redirect(request.referrer or url_for('dashboard'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# Adicione esta nova rota ao seu planner_app.py
@app.route('/consulta_fornecedores')
@login_requerido
@permissao_requerida('/cadastro_fornecedor') # Reutiliza a mesma permissão
def consulta_fornecedores():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        cursor_local.execute("SELECT * FROM TBL_Fornecedor ORDER BY NomeFantasia")
        fornecedores = cursor_local.fetchall()
        
        return render_template('consulta_fornecedor.html', fornecedores=fornecedores)

    except Exception as e:
        logger.error(f"Erro em /consulta_fornecedores: {e}", exc_info=True)
        flash("Ocorreu um erro ao carregar a página de fornecedores.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
@app.route('/cadastro_fornecedor', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_fornecedor')
def cadastro_fornecedor():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            id_fornecedor = request.form.get('id_fornecedor')
            codigo_fornecedor = request.form.get('codigo_fornecedor') # NOVO CAMPO
            nome_fantasia = request.form.get('nome_fantasia')
            razao_social = request.form.get('razao_social')
            cnpj = request.form.get('cnpj')
            contato = request.form.get('contato')
            email = request.form.get('email')
            telefone = request.form.get('telefone')
            endereco = request.form.get('endereco')
            ativo = 1 if 'ativo' in request.form else 0

            try:
                if id_fornecedor: # Lógica de ATUALIZAÇÃO
                    cursor_local.execute("""
                        UPDATE TBL_Fornecedor SET
                        CodigoFornecedor = ?, NomeFantasia = ?, RazaoSocial = ?, CNPJ = ?, 
                        ContatoPrincipal = ?, Email = ?, Telefone = ?, Endereco = ?, 
                        Ativo = ?, DataAtualizacao = GETDATE()
                        WHERE IDFornecedor = ?
                    """, (codigo_fornecedor, nome_fantasia, razao_social, cnpj, contato, email, telefone, endereco, ativo, id_fornecedor))
                    flash("Fornecedor atualizado com sucesso!", "success")
                else: # Lógica de INSERÇÃO
                    cursor_local.execute("""
                        INSERT INTO TBL_Fornecedor
                        (CodigoFornecedor, NomeFantasia, RazaoSocial, CNPJ, ContatoPrincipal, Email, Telefone, Endereco, Ativo)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """, (codigo_fornecedor, nome_fantasia, razao_social, cnpj, contato, email, telefone, endereco, ativo))
                    flash("Fornecedor cadastrado com sucesso!", "success")

                conn_local.commit()

            except pyodbc.IntegrityError:
                conn_local.rollback()
                flash(f"Erro: O Código do Fornecedor ou o CNPJ já está cadastrado no sistema.", "error")
            
            return redirect(url_for('consulta_fornecedores'))

        # Lógica GET
        id_edicao = request.args.get('id')
        fornecedor_para_editar = None
        if id_edicao:
            cursor_local.execute("SELECT * FROM TBL_Fornecedor WHERE IDFornecedor = ?", id_edicao)
            fornecedor_para_editar = cursor_local.fetchone()

        cursor_local.execute("SELECT * FROM TBL_Fornecedor ORDER BY NomeFantasia")
        fornecedores = cursor_local.fetchall()
        
        return render_template('cadastro_fornecedor.html',
                               fornecedores=fornecedores,
                               fornecedor_editar=fornecedor_para_editar)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em /cadastro_fornecedor: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar a página de fornecedores.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
# Em planner_app.py, SUBSTITUA a função da linha 7780:

@app.route('/relatorio_paradas/exportar', methods=['POST'])
@login_requerido
@permissao_requerida('/relatorio_paradas')
def exportar_relatorio_paradas():
    conn_local = None
    try:
        data = request.json
        export_type = data.get('exportType', 'ambos')
        filtros = {
            'data_inicio': data.get('data_inicio'),
            'data_fim': data.get('data_fim'),
            'id_maquina': data.get('id_maquina'),
            'id_turno': data.get('id_turno') 
        }

        # +++++ INÍCIO DA ALTERAÇÃO (LÓGICA DE DATA DE REFERÊNCIA) +++++

        data_inicio_dt = datetime.strptime(filtros['data_inicio'], '%Y-%m-%d')
        data_fim_dt = datetime.strptime(filtros['data_fim'], '%Y-%m-%d')
        conn_local = obter_conexao()

        # 1. Define o CTE base
        base_cte = """
            WITH StatusComDataTurno AS (
                SELECT 
                    SM.IDMaquina, SM.IDTurno, SM.DataHoraInicio, SM.DataHoraFim, 
                    SM.IDMotivoParada, SM.Status,
                    T.IniciaDiaAnterior, T.HoraInicio AS HoraInicioTurno,
                    CASE
                        WHEN T.IniciaDiaAnterior = 1 AND CAST(SM.DataHoraInicio AS TIME) < CAST(T.HoraInicio AS TIME)
                        THEN CAST(DATEADD(day, -1, SM.DataHoraInicio) AS DATE)
                        ELSE CAST(SM.DataHoraInicio AS DATE)
                    END AS DataReferenciaTurno
                FROM TBL_StatusMaquina SM
                LEFT JOIN TBL_Turno T ON SM.IDTurno = T.IDTurno
            )
        """
        
        # 2. Define o WHERE clause que filtra o CTE (para paradas)
        cte_where_clause = " WHERE SCDT.DataReferenciaTurno BETWEEN ? AND ? AND SCDT.Status = 0 AND SCDT.IDMotivoParada <> ?"
        params = [data_inicio_dt, data_fim_dt, ID_MOTIVO_FORA_DE_TURNO]

        if filtros['id_maquina']:
            cte_where_clause += " AND SCDT.IDMaquina = ?"
            params.append(int(filtros['id_maquina']))
        if filtros['id_turno']:
            cte_where_clause += " AND SCDT.IDTurno = ?"
            params.append(int(filtros['id_turno']))

        # 3. Query de Detalhes (usa o CTE)
        query = base_cte + f"""
            SELECT
                R.NomeMaquina, SCDT.DataHoraInicio, SCDT.DataHoraFim,
                DATEDIFF(SECOND, SCDT.DataHoraInicio, ISNULL(SCDT.DataHoraFim, GETDATE())) AS DuracaoSegundos,
                ISNULL(MP.Descricao, 'Não Classificada') AS MotivoParada
            FROM StatusComDataTurno SCDT
            JOIN TBL_Recurso R ON SCDT.IDMaquina = R.IDMaquina
            LEFT JOIN TBL_MotivoParada MP ON SCDT.IDMotivoParada = MP.IDMotivoParada
            {cte_where_clause} ORDER BY R.NomeMaquina, SCDT.DataHoraInicio
        """
        # +++++ FIM DA ALTERAÇÃO (LÓGICA DE DATA DE REFERÊNCIA) +++++

        df = pd.DataFrame()
        if export_type in ['tabela', 'ambos']:
            df_raw = pd.read_sql(query, conn_local, params=params)
            df_raw['Duração (HH:MM:SS)'] = df_raw['DuracaoSegundos'].apply(formatar_segundos_para_hms)
            df = df_raw[['NomeMaquina', 'DataHoraInicio', 'DataHoraFim', 'Duração (HH:MM:SS)', 'MotivoParada']]
            df.rename(columns={'NomeMaquina': 'Máquina', 'DataHoraInicio': 'Início', 'DataHoraFim': 'Fim', 'MotivoParada': 'Motivo'}, inplace=True)

        output = io.BytesIO()
        with pd.ExcelWriter(output, engine='openpyxl') as writer:
            df.to_excel(writer, index=False, sheet_name='Dados de Paradas')
            if export_type in ['grafico', 'ambos'] and 'chartImage' in data and data.get('chartImage'):
                try:
                    worksheet = writer.sheets['Dados de Paradas']
                    base64_image_data = data['chartImage'].split(',')[1]
                    image_data = base64.b64decode(base64_image_data)
                    img = Image(io.BytesIO(image_data))
                    img.anchor = 'A' + str(len(df) + 3)
                    worksheet.add_image(img)
                except Exception as img_err:
                    logger.error(f"Erro ao adicionar imagem (Paradas Export): {img_err}", exc_info=True)

        output.seek(0)
        return send_file(output, as_attachment=True, download_name='relatorio_paradas.xlsx',
                         mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet')

    except Exception as e:
        logger.error(f"Erro ao exportar relatório de paradas (com turno): {e}", exc_info=True)
        return jsonify({"error": "Falha ao gerar o arquivo Excel."}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
# planner_app.py (adicione este bloco e remova as rotas de exportação GET antigas)

# ###############################################################
# #####    NOVAS ROTAS AVANÇADAS PARA EXPORTAÇÃO EXCEL      #####
# ###############################################################

# Em planner_app.py, SUBSTITUA a função da linha 7872:

@app.route('/relatorio_producao/exportar', methods=['POST'])
@login_requerido
@permissao_requerida('/relatorio_producao')
def exportar_relatorio_producao():
    conn_local = None
    try:
        data = request.json
        export_type = data.get('exportType', 'ambos')
        filtros = {
            "data_inicio": data.get("data_inicio"), "data_fim": data.get("data_fim"),
            "id_maquina": data.get("id_maquina"), "id_produto": data.get("id_produto"),
            "id_operador": data.get("id_operador"), "codigo_ordem": data.get("codigo_ordem")
        }

        conn_local = obter_conexao()
        
        usa_unidades_caixa = obter_configuracao('USA_UNIDADES_POR_CAIXA', conn_local, conn_local.cursor()) == 'true'

        # +++++ INÍCIO DA ALTERAÇÃO (LÓGICA DE DATA DE REFERÊNCIA) +++++
        
        # 1. Define o CTE base
        base_cte = """
            WITH EventosComDataTurno AS (
                SELECT 
                    E.*, T.NomeTurno, T.IniciaDiaAnterior, T.HoraInicio AS HoraInicioTurno,
                    CASE
                        WHEN T.IniciaDiaAnterior = 1 AND CAST(E.DataHoraEvento AS TIME) < CAST(T.HoraInicio AS TIME)
                        THEN CAST(DATEADD(day, -1, E.DataHoraEvento) AS DATE)
                        ELSE CAST(E.DataHoraEvento AS DATE)
                    END AS DataReferenciaTurno
                FROM VW_EventoProducaoComCicloReal E
                LEFT JOIN TBL_Turno T ON E.IDTurno = T.IDTurno
                WHERE E.TipoValor IN ('BOA', 'REFUGO', 'ESTORNO')
            )
        """
        
        # 2. Query principal usa o CTE
        query = base_cte + '''
            SELECT 
                MIN(EVT.DataHoraEvento) AS DataHoraInicio, R.NomeMaquina, O.CodigoOrdem, P.CodigoProduto, P.NomeProduto,
                OPO.NumeroOperacao, OPO.Descricao AS DescricaoOperacao, 
                MAX(ISNULL(EVT.NomeTurno, 'Fora de Turno')) AS NomeTurno, O.QuantidadePlanejada, P.UnidadesPorCaixa,
                ISNULL(SUM(CASE WHEN EVT.TipoValor = 'BOA' THEN EVT.Quantidade ELSE 0 END), 0) AS QuantidadeProduzidaBruta,
                ISNULL(SUM(CASE WHEN EVT.TipoValor IN ('BOA', 'ESTORNO') THEN EVT.Quantidade ELSE 0 END), 0) AS QuantidadeProduzidaLiquida,
                ISNULL(SUM(CASE WHEN EVT.TipoValor = 'REFUGO' THEN EVT.Quantidade ELSE 0 END), 0) AS QuantidadeRefugada,
                Op.NomeOperador,
                EVT.DataReferenciaTurno -- Adicionado para o GROUP BY
            FROM EventosComDataTurno EVT
            JOIN TBL_ExecucaoOP EX ON EVT.IDExecucao = EX.IDExecucao
            JOIN TBL_OrdemProducao_Operacoes OPO ON EX.IDOrdemOperacao = OPO.IDOrdemOperacao
            JOIN TBL_Recurso R ON EVT.IDMaquina = R.IDMaquina
            JOIN TBL_OrdemProducao O ON EVT.IDOrdemProducao = O.IDOrdem
            JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
            LEFT JOIN TBL_Operador Op ON EVT.IDOperador = Op.IDOperador
            WHERE 1=1
        '''
        
        params = []
        if filtros["data_inicio"]: 
            data_inicio_obj = datetime.strptime(filtros["data_inicio"], "%Y-%m-%d")
            query += " AND EVT.DataReferenciaTurno >= ?"
            params.append(data_inicio_obj)
        if filtros["data_fim"]: 
            data_fim_obj = datetime.strptime(filtros["data_fim"], "%Y-%m-%d")
            query += " AND EVT.DataReferenciaTurno <= ?"
            params.append(data_fim_obj)
            
        # +++++ FIM DA ALTERAÇÃO (LÓGICA DE DATA DE REFERÊNCIA) +++++

        if filtros["id_maquina"]: query += " AND EVT.IDMaquina = ?"; params.append(int(filtros["id_maquina"]))
        if filtros["id_produto"]: query += " AND O.IDProduto = ?"; params.append(int(filtros["id_produto"]))
        if filtros["id_operador"]: query += " AND EVT.IDOperador = ?"; params.append(int(filtros["id_operador"]))
        if filtros["codigo_ordem"]: query += " AND O.CodigoOrdem LIKE ?"; params.append(f"%{filtros['codigo_ordem']}%")
        
        query += '''
            GROUP BY 
                EVT.DataReferenciaTurno, -- << Adicionado ao GROUP BY
                R.NomeMaquina, O.CodigoOrdem, P.CodigoProduto, P.NomeProduto,
                OPO.NumeroOperacao, OPO.Descricao,
                O.QuantidadePlanejada, Op.NomeOperador, P.UnidadesPorCaixa
            ORDER BY MIN(EVT.DataHoraEvento) DESC
        '''
        
        df = pd.DataFrame()
        if export_type in ['tabela', 'ambos']:
            df = pd.read_sql(query, conn_local, params=params)
            
            df['Operacao'] = df['NumeroOperacao'].astype(str) + ' - ' + df['DescricaoOperacao']

            if usa_unidades_caixa and not df.empty:
                df['Qtd. Caixas'] = df.apply(
                    lambda row: int(row['QuantidadeProduzidaLiquida'] // row['UnidadesPorCaixa']) if row['UnidadesPorCaixa'] and row['UnidadesPorCaixa'] > 0 else 0,
                    axis=1
                )

            colunas_rename = {
                'DataHoraInicio': 'Data Início', 'NomeMaquina': 'Máquina', 'CodigoOrdem': 'Cód. OP',
                'CodigoProduto': 'Cód. Produto', 'NomeProduto': 'Produto', 'Operacao': 'Operação', 'NomeTurno': 'Turno',
                'QuantidadePlanejada': 'Qtd. Planejada', 'QuantidadeProduzidaBruta': 'Qtd. Prod. (Bruta)',
                'QuantidadeProduzidaLiquida': 'Qtd. Prod. (Líq.)', 'QuantidadeRefugada': 'Qtd. Refugada',
                'NomeOperador': 'Operador'
            }
            df.rename(columns=colunas_rename, inplace=True)
            
            colunas_finais = [
                'Data Início', 'Máquina', 'Cód. OP', 'Cód. Produto', 'Produto', 'Operação', 'Turno',
                'Qtd. Planejada', 'Qtd. Prod. (Bruta)', 'Qtd. Refugada', 'Qtd. Prod. (Líq.)'
            ]
            if usa_unidades_caixa and 'Qtd. Caixas' in df.columns:
                colunas_finais.append('Qtd. Caixas')
            
            colunas_finais.append('Operador')
            
            df = df[[col for col in colunas_finais if col in df.columns]]

            if 'Data Início' in df.columns:
                df['Data Início'] = pd.to_datetime(df['Data Início']).dt.strftime('%d/%m/%Y %H:%M')
        
        output = io.BytesIO()
        with pd.ExcelWriter(output, engine='openpyxl') as writer:
            df.to_excel(writer, index=False, sheet_name='Produção')
            if export_type in ['grafico', 'ambos']:
                worksheet = writer.sheets['Produção']
                if 'chartImage' in data and data['chartImage']:
                    base64_image_data = data['chartImage'].split(',')[1]
                    image_data = base64.b64decode(base64_image_data)
                    img = Image(io.BytesIO(image_data))
                    img.anchor = 'A' + str(len(df) + 3)
                    worksheet.add_image(img)
        
        output.seek(0)
        return send_file(output, as_attachment=True, download_name='relatorio_producao.xlsx', 
                         mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet')
    except Exception as e:
        logger.error(f"Erro ao exportar relatório de produção (avançado): {e}", exc_info=True)
        return jsonify({"error": "Falha ao gerar o arquivo Excel."}), 500
    finally:
        if conn_local: devolver_conexao(conn_local)

# Em planner_app.py, SUBSTITUA a função da linha 7977:

@app.route('/relatorio_refugos/exportar', methods=['POST'])
@login_requerido
@permissao_requerida('/relatorio_refugos')
def exportar_relatorio_refugos():
    conn_local = None
    try:
        data = request.json
        export_type = data.get('exportType', 'ambos')
        data_inicio = data.get('data_inicio')
        data_fim = data.get('data_fim')
        codigo_ordem = data.get('codigo_ordem')

        data_inicio_dt = validar_data(data_inicio)
        data_fim_dt = validar_data(data_fim)

        base_cte = """
            WITH EventosComDataTurno AS (
                SELECT 
                    E.*, T.NomeTurno, T.IniciaDiaAnterior, T.HoraInicio AS HoraInicioTurno,
                    CASE
                        WHEN T.IniciaDiaAnterior = 1 AND CAST(E.DataHoraEvento AS TIME) < CAST(T.HoraInicio AS TIME)
                        THEN CAST(DATEADD(day, -1, E.DataHoraEvento) AS DATE)
                        ELSE CAST(E.DataHoraEvento AS DATE)
                    END AS DataReferenciaTurno
                FROM VW_EventoProducaoComCicloReal E
                LEFT JOIN TBL_Turno T ON E.IDTurno = T.IDTurno
                WHERE E.TipoValor = 'REFUGO'
            )
        """
        
        from_where_clause = """
            FROM EventosComDataTurno EVT
            JOIN TBL_OrdemProducao O ON O.IDOrdem = EVT.IDOrdemProducao
            JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
            JOIN TBL_Recurso R ON R.IDMaquina = EVT.IDMaquina
            LEFT JOIN TBL_MotivoRefugo MR ON MR.IDMotivoRefugo = EVT.IDMotivoRefugo
            WHERE EVT.DataReferenciaTurno BETWEEN ? AND ?
        """
        params = [data_inicio_dt, data_fim_dt]
        if codigo_ordem: 
            from_where_clause += " AND O.CodigoOrdem = ?"
            params.append(codigo_ordem)
        
        conn_local = obter_conexao()
        df = pd.DataFrame()
        if export_type in ['tabela', 'ambos']:
            query_detalhes = base_cte + f"""
                SELECT O.CodigoOrdem, P.CodigoProduto, P.NomeProduto, EVT.DataHoraEvento, 
                       R.NomeMaquina, EVT.Quantidade, MR.Descricao AS MotivoRefugo,
                       EVT.ObsEvento -- << CAMPO ADICIONADO
                {from_where_clause} ORDER BY O.CodigoOrdem, EVT.DataHoraEvento
            """
            df = pd.read_sql(query_detalhes, conn_local, params=params)
            df.rename(columns={
                'CodigoOrdem': 'OP', 'CodigoProduto': 'Cód. Produto', 'NomeProduto': 'Produto', 'DataHoraEvento': 'Data/Hora',
                'NomeMaquina': 'Máquina', 'Quantidade': 'Quantidade', 'MotivoRefugo': 'Motivo do Refugo',
                'ObsEvento': 'Observação' 
            }, inplace=True)
        
        output = io.BytesIO()
        with pd.ExcelWriter(output, engine='openpyxl') as writer:
            df.to_excel(writer, index=False, sheet_name='Refugos')
            if export_type in ['grafico', 'ambos']:
                worksheet = writer.sheets['Refugos']
                base64_image_data = data.get('chartImage').split(',')[1]
                image_data = base64.b64decode(base64_image_data)
                img = Image(io.BytesIO(image_data))
                img.anchor = 'A' + str(len(df) + 3)
                worksheet.add_image(img)

        output.seek(0)
        return send_file(output, as_attachment=True, download_name='relatorio_de_refugos.xlsx', 
                         mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet')
    except Exception as e:
        logger.error(f"Erro ao exportar relatório de refugos (avançado): {e}", exc_info=True)
        return jsonify({"error": "Falha ao gerar o arquivo Excel."}), 500
    finally:
        if conn_local: devolver_conexao(conn_local)


# Em planner_app.py, SUBSTITUA a função da linha 8056:

@app.route('/relatorio_status/exportar', methods=['POST'])
@login_requerido
@permissao_requerida('/relatorio_status')
def exportar_relatorio_status():
    conn_local = None
    try:
        data = request.json
        export_type = data.get('exportType', 'ambos')
        filtros = {
            "data_inicio": data.get("data_inicio"),
            "data_fim": data.get("data_fim"),
            "id_maquina": data.get("id_maquina"),
            "id_turno": data.get("id_turno") 
        }

        conn_local = obter_conexao()

        # +++++ INÍCIO DA ALTERAÇÃO (LÓGICA DE DATA DE REFERÊNCIA) +++++

        # 1. CTE para calcular a Data de Referência do Turno
        query = """
            WITH StatusComDataTurno AS (
                SELECT 
                    SM.*,
                    T.IniciaDiaAnterior, T.HoraInicio AS HoraInicioTurno,
                    CASE
                        WHEN T.IniciaDiaAnterior = 1 AND CAST(SM.DataHoraInicio AS TIME) < CAST(T.HoraInicio AS TIME)
                        THEN CAST(DATEADD(day, -1, SM.DataHoraInicio) AS DATE)
                        ELSE CAST(SM.DataHoraInicio AS DATE)
                    END AS DataReferenciaTurno
                FROM TBL_StatusMaquina SM
                LEFT JOIN TBL_Turno T ON SM.IDTurno = T.IDTurno
            )
        -- 2. Query principal agora filtra pela DataReferenciaTurno
        SELECT
            COALESCE(MP.Descricao, TS.NomeStatus, 'N/A') AS MotivoOuStatus,
            SCDT.DataHoraInicio,
            ISNULL(SCDT.DataHoraFim, GETDATE()) AS DataHoraFim,
            DATEDIFF(SECOND, SCDT.DataHoraInicio, ISNULL(SCDT.DataHoraFim, GETDATE())) AS DuracaoSegundos,
            ExecInfo.CodigoOrdem, ExecInfo.NomeProduto,
            SCDT.ObsEvento
        FROM StatusComDataTurno SCDT
        JOIN TBL_TipoStatus TS ON SCDT.Status = TS.Status
        LEFT JOIN TBL_MotivoParada MP ON SCDT.IDMotivoParada = MP.IDMotivoParada
        OUTER APPLY (
            SELECT TOP 1 OP.CodigoOrdem, P.NomeProduto
            FROM TBL_ExecucaoOP EX
            JOIN TBL_OrdemProducao OP ON EX.IDOrdem = OP.IDOrdem
            JOIN TBL_Produto P ON OP.IDProduto = P.IDProduto
            WHERE EX.IDMaquina = SCDT.IDMaquina AND SCDT.DataHoraInicio >= EX.DataHoraInicio AND (SCDT.DataHoraInicio < EX.DataHoraFim OR EX.DataHoraFim IS NULL)
            ORDER BY EX.DataHoraInicio DESC
        ) AS ExecInfo
        WHERE SCDT.IDMaquina = ?
          AND ISNULL(SCDT.IDMotivoParada, -1) <> ?
        """

        data_inicio_dt = datetime.strptime(filtros["data_inicio"], "%Y-%m-%d")
        data_fim_dt = datetime.strptime(filtros["data_fim"], "%Y-%m-%d")
        
        # 3. Adiciona os filtros de data (usando DataReferenciaTurno)
        query += " AND SCDT.DataReferenciaTurno BETWEEN ? AND ?"
        params = [int(filtros["id_maquina"]), ID_MOTIVO_FORA_DE_TURNO, data_inicio_dt, data_fim_dt]

        # +++++ FIM DA ALTERAÇÃO (LÓGICA DE DATA DE REFERÊNCIA) +++++

        if filtros["id_turno"]:
            query += " AND SCDT.IDTurno = ?"
            params.append(int(filtros["id_turno"]))

        query += " ORDER BY SCDT.DataHoraInicio ASC"

        df = pd.DataFrame()
        if export_type in ['tabela', 'ambos']:
            df_raw = pd.read_sql(query, conn_local, params=params)
            df_raw['Duração (HH:MM:SS)'] = df_raw['DuracaoSegundos'].apply(formatar_segundos_para_hms)
            df = df_raw[['MotivoOuStatus', 'DataHoraInicio', 'DataHoraFim', 'Duração (HH:MM:SS)', 'CodigoOrdem', 'NomeProduto', 'ObsEvento']]
            df.rename(columns={ 'MotivoOuStatus': 'Status / Motivo', 'DataHoraInicio': 'Início', 'DataHoraFim': 'Fim', 'CodigoOrdem': 'Ordem', 'NomeProduto': 'Produto', 'ObsEvento': 'Observação' }, inplace=True)


        output = io.BytesIO()
        with pd.ExcelWriter(output, engine='openpyxl') as writer:
            df.to_excel(writer, index=False, sheet_name='Status')
            if export_type in ['grafico', 'ambos'] and 'chartImage' in data and data.get('chartImage'):
                 try:
                    worksheet = writer.sheets['Status']
                    base64_image_data = data['chartImage'].split(',')[1]
                    image_data = base64.b64decode(base64_image_data)
                    img = Image(io.BytesIO(image_data))
                    img.anchor = 'A' + str(len(df) + 3)
                    worksheet.add_image(img)
                 except Exception as img_err:
                    logger.error(f"Erro ao adicionar imagem (Status Export): {img_err}", exc_info=True)


        output.seek(0)
        return send_file(output, as_attachment=True, download_name='relatorio_status_maquina.xlsx',
                         mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet')

    except Exception as e:
        logger.error(f"Erro ao exportar relatório de status (com turno): {e}", exc_info=True)
        return jsonify({"error": "Falha ao gerar o arquivo Excel."}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
 
# planner_app.py (adicione esta nova rota ao final do arquivo)

@app.route('/relatorio_estornos/exportar', methods=['POST'])
@login_requerido
@permissao_requerida('/relatorio_estornos')
def exportar_relatorio_estornos():
    conn_local = None
    try:
        data = request.json
        filtros = { "data_inicio": data.get("data_inicio"), "data_fim": data.get("data_fim") }
        data_inicio_dt = datetime.strptime(filtros["data_inicio"], "%Y-%m-%d")
        data_fim_dt = datetime.strptime(filtros["data_fim"], "%Y-%m-%d").replace(hour=23, minute=59, second=59)
        conn_local = obter_conexao()
        
        # --- ALTERAÇÃO AQUI: Adicionada subquery de Produção Líquida na exportação ---
        query = """
            SELECT 
                E.DataHoraEvento, R.NomeMaquina, P.NomeProduto, OP.CodigoOrdem, OP.QuantidadePlanejada,
                ISNULL((SELECT SUM(gross.Quantidade) 
                    FROM VW_EventoProducaoComCicloReal gross 
                    WHERE gross.IDOrdemProducao = E.IDOrdemProducao AND gross.TipoValor = 'BOA'
                ), 0) AS QuantidadeProduzidaBruta,
                ISNULL((SELECT SUM(net.Quantidade) 
                    FROM VW_EventoProducaoComCicloReal net 
                    WHERE net.IDOrdemProducao = E.IDOrdemProducao AND net.TipoValor IN ('BOA', 'ESTORNO')
                ), 0) AS QuantidadeProduzidaLiquida,
                ISNULL((SELECT SUM(scrap.Quantidade)
                    FROM VW_EventoProducaoComCicloReal scrap
                    WHERE scrap.IDOrdemProducao = E.IDOrdemProducao AND scrap.TipoValor = 'REFUGO'
                ), 0) AS QuantidadeRefugadaTotal,
                -E.Quantidade AS QuantidadeEstornada,
                E.ObsEvento AS MotivoEstorno,
                U.NomeUsuario AS NomeOperador
            FROM VW_EventoProducaoComCicloReal E
            JOIN TBL_OrdemProducao OP ON E.IDOrdemProducao = OP.IDOrdem
            JOIN TBL_Produto P ON OP.IDProduto = P.IDProduto
            JOIN TBL_Recurso R ON E.IDMaquina = R.IDMaquina
            LEFT JOIN TBL_Usuario U ON E.IDOperador = U.IDUsuario
            WHERE E.TipoValor = 'ESTORNO' AND E.DataHoraEvento BETWEEN ? AND ?
            ORDER BY E.DataHoraEvento DESC
        """
        
        df = pd.read_sql(query, conn_local, params=(data_inicio_dt, data_fim_dt))

        df.rename(columns={
            'DataHoraEvento': 'Data/Hora', 'NomeMaquina': 'Máquina', 'NomeProduto': 'Produto',
            'CodigoOrdem': 'Ordem', 'QuantidadePlanejada': 'Qtd. Planejada',
            'QuantidadeProduzidaBruta': 'Qtd. Produzida (Bruta)',
            'QuantidadeProduzidaLiquida': 'Qtd. Produzida (Líq.)', # Nova coluna no Excel
            'QuantidadeRefugadaTotal': 'Qtd. Refugada (Total OP)',
            'QuantidadeEstornada': 'Qtd. Estornada',
            'MotivoEstorno': 'Motivo do Estorno', 'NomeOperador': 'Operador'
        }, inplace=True)

        output = io.BytesIO()
        df.to_excel(output, index=False, sheet_name='Estornos')
        output.seek(0)
        
        return send_file(output, as_attachment=True, download_name='relatorio_estornos.xlsx', 
                         mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet')
    except Exception as e:
        logger.error(f"Erro ao exportar relatório de estornos: {e}", exc_info=True)
        return jsonify({"error": "Falha ao gerar o arquivo Excel."}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

            
# Rota para o cadastro de Unidade de Medida
@app.route('/cadastro_unidade_medida', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_unidade_medida') # Lembre-se de adicionar esta permissão no sistema
def cadastro_unidade_medida():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Lógica para salvar (POST)
        if request.method == 'POST':
            id_unidade = request.form.get('id_unidade')
            nome = request.form.get('nome').strip()
            sigla = request.form.get('sigla').strip()
            codigo = request.form.get('codigo').strip()
            ativo = 1 if 'ativo' in request.form else 0

            if id_unidade:
                # ATUALIZAR registro existente
                cursor_local.execute("""
                    UPDATE TBL_UnidadeMedida
                    SET NomeUnidade = ?, Sigla = ?, Codigo = ?, Ativo = ?
                    WHERE IDUnidade = ?
                """, (nome, sigla, codigo, ativo, id_unidade))
                flash("Unidade de medida atualizada com sucesso!", "success")
            else:
                # INSERIR novo registro
                cursor_local.execute("""
                    INSERT INTO TBL_UnidadeMedida (NomeUnidade, Sigla, Codigo, Ativo, DtCriacao)
                    VALUES (?, ?, ?, ?, GETDATE())
                """, (nome, sigla, codigo, ativo))
                flash("Unidade de medida cadastrada com sucesso!", "success")

            conn_local.commit()
            return redirect(url_for('cadastro_unidade_medida'))

        # Lógica para carregar a página (GET)
        id_edicao = request.args.get('id')
        unidade_para_editar = None
        if id_edicao:
            cursor_local.execute("SELECT * FROM TBL_UnidadeMedida WHERE IDUnidade = ?", id_edicao)
            unidade_para_editar = cursor_local.fetchone()

        cursor_local.execute("SELECT * FROM TBL_UnidadeMedida ORDER BY NomeUnidade")
        unidades = cursor_local.fetchall()

        return render_template('cadastro_unidade_medida.html', 
                               unidades=unidades, 
                               unidade=unidade_para_editar)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em cadastro_unidade_medida: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar a página de unidades de medida.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
@app.route('/relatorio_rastreabilidade', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relatorio_rastreabilidade')
def relatorio_rastreabilidade():
    conn_local = None
    resultados = []
    
    filtros = {
        "data_inicio": (datetime.now() - timedelta(days=7)).strftime('%Y-%m-%d'),
        "data_fim": datetime.now().strftime('%Y-%m-%d'),
        "id_produto": request.form.get("id_produto"),
        "id_materia_prima": request.form.get("id_materia_prima")
    }

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("SELECT IDProduto, NomeProduto FROM TBL_Produto WHERE Habilitado = 1 ORDER BY NomeProduto")
        produtos = cursor_local.fetchall()
        cursor_local.execute("SELECT IDMateriaPrima, NomeMateriaPrima FROM TBL_MateriaPrima WHERE Ativo = 1 ORDER BY NomeMateriaPrima")
        materias_primas = cursor_local.fetchall()

        if request.method == 'POST':
            filtros["data_inicio"] = request.form.get("data_inicio")
            filtros["data_fim"] = request.form.get("data_fim")

            query = """
                SELECT
                    P.NomeProduto AS ProdutoAcabado,
                    OP.CodigoOrdem,
                    MP.NomeMateriaPrima,
                    MP.IDMateriaPrima, 
                    L.Lote AS LoteMateriaPrima,
                    F.NomeFantasia AS Fornecedor,
                    L.DataHoraEvento AS DataConsumo,
                    R.NomeMaquina AS Recurso
                FROM TBL_LogMovimentacaoEstoque L
                JOIN TBL_MateriaPrima MP ON L.IDMateriaPrima = MP.IDMateriaPrima
                LEFT JOIN TBL_UnidadeMedida UM ON MP.IDUnidade = UM.IDUnidade
                JOIN TBL_ExecucaoOP E ON L.IDExecucaoOP = E.IDExecucao
                JOIN TBL_OrdemProducao OP ON E.IDOrdem = OP.IDOrdem
                JOIN TBL_Produto P ON OP.IDProduto = P.IDProduto
                JOIN TBL_Recurso R ON E.IDMaquina = R.IDMaquina
                LEFT JOIN TBL_Fornecedor F ON L.IDFornecedor = F.IDFornecedor
                WHERE L.TipoMovimento = 'CONSUMO_PRODUCAO'
            """
            params = []

            if filtros["data_inicio"]:
                query += " AND CAST(L.DataHoraEvento AS DATE) >= ?"
                params.append(filtros["data_inicio"])
            if filtros["data_fim"]:
                query += " AND CAST(L.DataHoraEvento AS DATE) <= ?"
                params.append(filtros["data_fim"])
            if filtros["id_produto"]:
                query += " AND P.IDProduto = ?"
                params.append(filtros["id_produto"])
            if filtros["id_materia_prima"]:
                query += " AND MP.IDMateriaPrima = ?"
                params.append(filtros["id_materia_prima"])

            query += " ORDER BY L.DataHoraEvento DESC"
            cursor_local.execute(query, params)
            resultados = cursor_local.fetchall()
        
        return render_template("relatorio_rastreabilidade.html",
                               resultados=resultados,
                               filtros=filtros,
                               produtos=produtos,
                               materias_primas=materias_primas)
    except Exception as e:
        logger.error(f"Erro em relatorio_rastreabilidade: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerar o relatório de rastreabilidade.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/relatorio_rastreabilidade/exportar', methods=['POST'])
@login_requerido
@permissao_requerida('/relatorio_rastreabilidade')
def exportar_relatorio_rastreabilidade():
    conn_local = None
    try:
        filtros = request.get_json()
        conn_local = obter_conexao()
        
        query = """
            SELECT
                P.NomeProduto AS [Produto Acabado],
                OP.CodigoOrdem AS [Ordem / Lote PA],
                MP.NomeMateriaPrima AS [Matéria-Prima],
                L.Lote AS [Lote MP],
                F.NomeFantasia AS [Fornecedor],
                L.DataHoraEvento AS [Data Consumo],
                R.NomeMaquina AS [Recurso]
            FROM TBL_LogMovimentacaoEstoque L
            JOIN TBL_MateriaPrima MP ON L.IDMateriaPrima = MP.IDMateriaPrima
            JOIN TBL_ExecucaoOP E ON L.IDExecucaoOP = E.IDExecucao
            JOIN TBL_OrdemProducao OP ON E.IDOrdem = OP.IDOrdem
            JOIN TBL_Produto P ON OP.IDProduto = P.IDProduto
            JOIN TBL_Recurso R ON E.IDMaquina = R.IDMaquina
            LEFT JOIN TBL_Fornecedor F ON L.IDFornecedor = F.IDFornecedor
            WHERE L.TipoMovimento = 'CONSUMO_PRODUCAO'
        """
        params = []

        if filtros.get("data_inicio"):
            query += " AND CAST(L.DataHoraEvento AS DATE) >= ?"
            params.append(filtros["data_inicio"])
        if filtros.get("data_fim"):
            query += " AND CAST(L.DataHoraEvento AS DATE) <= ?"
            params.append(filtros["data_fim"])
        if filtros.get("id_produto"):
            query += " AND P.IDProduto = ?"
            params.append(filtros["id_produto"])
        if filtros.get("id_materia_prima"):
            query += " AND MP.IDMateriaPrima = ?"
            params.append(filtros["id_materia_prima"])

        query += " ORDER BY L.DataHoraEvento DESC"
        
        df = pd.read_sql_query(query, conn_local, params=params)
        
        output = io.BytesIO()
        with pd.ExcelWriter(output, engine='openpyxl') as writer:
            df.to_excel(writer, index=False, sheet_name='Rastreabilidade')
        
        output.seek(0)
        
        return send_file(
            output,
            mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
            as_attachment=True,
            download_name='relatorio_de_rastreabilidade.xlsx'
        )
    except Exception as e:
        logger.error(f"Erro ao exportar relatório de rastreabilidade: {e}", exc_info=True)
        return jsonify({"error": "Falha ao gerar o arquivo"}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# Adicione esta nova rota ao seu planner_app.py
@app.route('/api/detalhes_lote_mp')
@login_requerido
def api_detalhes_lote_mp():
    conn_local = None
    try:
        # Pega os parâmetros da URL (ex: ?lote=L-0509&id_mp=7)
        lote = request.args.get('lote')
        id_materia_prima = request.args.get('id_mp', type=int)

        if not lote or not id_materia_prima:
            return jsonify({"error": "Parâmetros 'lote' e 'id_mp' são obrigatórios."}), 400

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Procura pelo evento de ENTRADA_MANUAL para este lote específico
        cursor_local.execute("""
            SELECT TOP 1
                L.DataHoraEvento,
                L.Quantidade,
                L.NumeroNotaFiscal,
                U.NomeUsuario AS NomeUsuarioRegistro,
                F.NomeFantasia AS NomeFornecedor
            FROM TBL_LogMovimentacaoEstoque L
            LEFT JOIN TBL_Usuario U ON L.IDUsuario = U.IDUsuario
            LEFT JOIN TBL_Fornecedor F ON L.IDFornecedor = F.IDFornecedor
            WHERE L.IDMateriaPrima = ? 
              AND L.Lote = ? 
              AND L.TipoMovimento = 'ENTRADA_MANUAL'
            ORDER BY L.DataHoraEvento ASC
        """, (id_materia_prima, lote))
        
        detalhes = cursor_local.fetchone()

        if not detalhes:
            return jsonify({"error": "Nenhum registo de entrada encontrado para este lote."}), 404

        # Constrói o objeto de resposta
        resultado = {
            "data_entrada": detalhes.DataHoraEvento.strftime('%d/%m/%Y %H:%M:%S'),
            "quantidade_entrada": ("%g" % detalhes.Quantidade).replace('.', ','),
            "nota_fiscal": detalhes.NumeroNotaFiscal or "Não informada",
            "registrado_por": detalhes.NomeUsuarioRegistro or "Sistema",
            "fornecedor": detalhes.NomeFornecedor or "Não informado"
        }
        return jsonify(resultado)

    except Exception as e:
        logger.error(f"Erro em /api/detalhes_lote_mp: {e}", exc_info=True)
        return jsonify({"error": "Erro interno do servidor"}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)  

# planner_app.py

@app.route('/relatorio_producao_horaria', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relatorio_producao_horaria')
def relatorio_producao_horaria():
    conn_local = None
    resultados = []
    
    filtros = {
        "data_inicio": request.form.get("data_inicio", datetime.now().strftime('%Y-%m-%d')),
        "data_fim": request.form.get("data_fim", datetime.now().strftime('%Y-%m-%d')),
        "id_recurso": request.form.get("id_recurso"),
        "id_produto": request.form.get("id_produto"),
        "agrupar_por": request.form.get("agrupar_por", "recurso")
    }

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        maquinas = cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina").fetchall()
        produtos = cursor_local.execute("SELECT IDProduto, CodigoProduto, NomeProduto FROM TBL_Produto WHERE Habilitado = 1 ORDER BY NomeProduto").fetchall()

        if request.method == 'POST':
            select_clause = ""
            group_by_clause = ""
            
            if filtros['agrupar_por'] == 'recurso':
                select_clause = "CAST(SM.DataHoraInicio AS DATE) AS Data, R.NomeMaquina"
                group_by_clause = "CAST(SM.DataHoraInicio AS DATE), R.NomeMaquina"
            elif filtros['agrupar_por'] == 'produto':
                select_clause = "CAST(SM.DataHoraInicio AS DATE) AS Data, P.CodigoProduto, P.NomeProduto"
                group_by_clause = "CAST(SM.DataHoraInicio AS DATE), P.CodigoProduto, P.NomeProduto"
            elif filtros['agrupar_por'] == 'ordem':
                select_clause = "CAST(SM.DataHoraInicio AS DATE) AS Data, O.CodigoOrdem, P.CodigoProduto, P.NomeProduto"
                group_by_clause = "CAST(SM.DataHoraInicio AS DATE), O.CodigoOrdem, P.CodigoProduto, P.NomeProduto"

            query = f"""
                WITH ProducaoEventos AS (
                    SELECT 
                        IDExecucao,
                        SUM(CASE WHEN TipoValor IN ('BOA', 'ESTORNO') THEN Quantidade ELSE 0 END) as QtdProduzida
                    FROM VW_EventoProducaoComCicloReal
                    WHERE DataHoraEvento BETWEEN ? AND ?
                    GROUP BY IDExecucao
                )
                SELECT 
                    {select_clause},
                    SUM(PE.QtdProduzida) as QuantidadeProduzida,
                    SUM(DATEDIFF(SECOND, SM.DataHoraInicio, ISNULL(SM.DataHoraFim, GETDATE()))) AS TempoProducaoSegundos,
                    MAX(P.TempoCicloSegundos) as TempoCicloPadrao,
                    MAX(P.FatorMultiplicacao) as FatorMultiplicacaoPadrao
                FROM TBL_StatusMaquina SM
                JOIN TBL_ExecucaoOP EX ON SM.IDMaquina = EX.IDMaquina 
                    AND SM.DataHoraInicio BETWEEN EX.DataHoraInicio AND ISNULL(EX.DataHoraFim, GETDATE())
                JOIN ProducaoEventos PE ON EX.IDExecucao = PE.IDExecucao
                JOIN TBL_OrdemProducao O ON EX.IDOrdem = O.IDOrdem
                JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
                JOIN TBL_Recurso R ON SM.IDMaquina = R.IDMaquina
                WHERE SM.Status = 1
            """
            
            params = [
                datetime.strptime(filtros["data_inicio"], "%Y-%m-%d"),
                datetime.strptime(filtros["data_fim"], "%Y-%m-%d").replace(hour=23, minute=59, second=59)
            ]

            if filtros["id_recurso"]: query += " AND R.IDMaquina = ?"; params.append(int(filtros["id_recurso"]))
            if filtros["id_produto"]: query += " AND P.IDProduto = ?"; params.append(int(filtros["id_produto"]))
            
            query += f" GROUP BY {group_by_clause} ORDER BY Data DESC"
            
            cursor_local.execute(query, params)
            resultados_raw = [dict(zip([column[0] for column in cursor_local.description], row)) for row in cursor_local.fetchall()]
            
            for res in resultados_raw:
                # --- CORREÇÃO APLICADA AQUI ---
                # Convertendo todos os valores numéricos para float antes dos cálculos
                qtd_produzida = float(res['QuantidadeProduzida'] or 0)
                tempo_seg = float(res['TempoProducaoSegundos'] or 0)
                ciclo_padrao = float(res['TempoCicloPadrao'] or 0)
                fator_mult = float(res['FatorMultiplicacaoPadrao'] or 1)
                
                tempo_h = tempo_seg / 3600.0
                res['TempoProducaoHoras'] = round(tempo_h, 2)
                
                res['ProdHorariaReal'] = round(qtd_produzida / tempo_h, 2) if tempo_h > 0 else 0
                
                res['ProdHorariaPrevista'] = round((3600.0 / ciclo_padrao) * fator_mult, 2) if ciclo_padrao > 0 else 0
                
                res['Performance'] = round((res['ProdHorariaReal'] / res['ProdHorariaPrevista']) * 100, 2) if res['ProdHorariaPrevista'] > 0 else 0
                
                resultados.append(res)
                
        return render_template("relatorio_producao_horaria.html", 
                               resultados=resultados, filtros=filtros, maquinas=maquinas, produtos=produtos)
    except Exception as e:
        logger.error(f"Erro em relatorio_producao_horaria: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerar o relatório.", "error")
        return redirect(url_for('relatorios'))
    finally:
        if conn_local:
            devolver_conexao(conn_local) 

@app.route('/saida_produto_acabado', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/saida_produto_acabado')
def saida_produto_acabado():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            id_estoque_pa = request.form.get('id_estoque_pa')
            quantidade_saida_str = request.form.get('quantidade_saida', '0').replace(',', '.')
            quantidade_saida = float(quantidade_saida_str)
            destino = request.form.get('destino')
            documento = request.form.get('documento')
            id_usuario = session.get('usuario_id')

            if not id_estoque_pa or quantidade_saida <= 0:
                flash("É obrigatório selecionar um lote e informar uma quantidade maior que zero.", "error")
                return redirect(url_for('saida_produto_acabado'))

            cursor_local.execute(
                "SELECT QuantidadeDisponivel, IDProduto, Lote FROM TBL_EstoqueProdutoAcabado WHERE IDEstoquePA = ?", 
                id_estoque_pa
            )
            lote_info = cursor_local.fetchone()

            if not lote_info or float(lote_info.QuantidadeDisponivel) < quantidade_saida:
                flash("Erro: A quantidade de saída não pode ser maior que a quantidade disponível no lote.", "error")
                return redirect(url_for('saida_produto_acabado'))

            nova_quantidade = float(lote_info.QuantidadeDisponivel) - quantidade_saida
            cursor_local.execute(
                "UPDATE TBL_EstoqueProdutoAcabado SET QuantidadeDisponivel = ? WHERE IDEstoquePA = ?",
                (nova_quantidade, id_estoque_pa)
            )
            
            obs = f"Saída para: {destino or 'N/D'}. Documento: {documento or 'N/D'}"
            
            # --- CORREÇÃO AQUI: Usa a nova coluna IDEstoquePA ---
            cursor_local.execute("""
                INSERT INTO TBL_LogMovimentacaoEstoque 
                (IDEstoquePA, IDProduto, Lote, TipoMovimento, Quantidade, IDUsuario, Observacao)
                VALUES (?, ?, ?, 'SAIDA_EXPEDICAO', ?, ?, ?)
            """, (id_estoque_pa, lote_info.IDProduto, lote_info.Lote, -quantidade_saida, id_usuario, obs))
            
            conn_local.commit()
            flash(f"Saída de {quantidade_saida} unidades do lote {lote_info.Lote} registada com sucesso!", "success")
            return redirect(url_for('saida_produto_acabado'))

        # A lógica GET continua igual
        cursor_local.execute("""
            SELECT E.IDEstoquePA, P.NomeProduto, E.Lote, E.QuantidadeDisponivel, UM.Sigla
            FROM TBL_EstoqueProdutoAcabado E
            JOIN TBL_Produto P ON E.IDProduto = P.IDProduto
            LEFT JOIN TBL_UnidadeMedida UM ON P.IDUnidade = UM.IDUnidade
            WHERE E.QuantidadeDisponivel > 0
            ORDER BY P.NomeProduto, E.Lote
        """)
        lotes_disponiveis = cursor_local.fetchall()

        return render_template('saida_produto_acabado.html', lotes_disponiveis=lotes_disponiveis)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em /saida_produto_acabado: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar a página de saída de estoque.", "error")
        return redirect(url_for('estoque_dashboard'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)   

@app.route('/api/reclassificar_parada_anterior', methods=['POST'])
@login_requerido
def api_reclassificar_parada_anterior():
    conn_local = None
    try:
        data = request.json
        id_registro_status = data.get('id_registro_status')
        id_novo_motivo = data.get('id_novo_motivo')
        
        # Recebe a observação digitada no modal (se houver)
        observacao_usuario = data.get('observacao', '').strip()

        if not id_registro_status or not id_novo_motivo:
            return jsonify({'success': False, 'message': 'Dados incompletos.'}), 400

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # 1. Busca a descrição do novo motivo escolhido
        cursor_local.execute("SELECT Descricao FROM TBL_MotivoParada WHERE IDMotivoParada = ?", id_novo_motivo)
        motivo_row = cursor_local.fetchone()
        nome_motivo = motivo_row.Descricao if motivo_row else "Motivo Desconhecido"

        # --- AQUI ESTÁ A CORREÇÃO DO TEXTO ---
        # Forçamos o prefixo "Reclassificada como:" antes do nome do motivo
        texto_padrao = f"Reclassificada como: {nome_motivo}"

        if observacao_usuario:
            # Se o usuário digitou algo: "Reclassificada como: FALTA DE ENERGIA - Obs: Teste"
            obs_final = f"{texto_padrao} - Obs: {observacao_usuario}"
        else:
            # Se não digitou nada: "Reclassificada como: FALTA DE ENERGIA"
            obs_final = texto_padrao
        # -------------------------------------

        # 2. Atualiza o registro da parada antiga no banco
        cursor_local.execute("""
            UPDATE TBL_StatusMaquina
            SET IDMotivoParada = ?, ObsEvento = ?
            WHERE IDRegistroStatus = ? 
            -- Removemos a trava 'AND IDMotivoParada = 2' para permitir reclassificar mesmo se já foi mexido antes, 
            -- ou mantenha se quiser restringir apenas a paradas não identificadas.
            -- Sugestão: Deixe sem a trava para permitir corrigir erros de classificação.
            AND IDRegistroStatus = ? 
        """, (id_novo_motivo, obs_final, id_registro_status, id_registro_status))

        if cursor_local.rowcount == 0:
            # Tenta sem o WHERE IDRegistroStatus duplicado, só pra garantir
            cursor_local.execute("""
                UPDATE TBL_StatusMaquina
                SET IDMotivoParada = ?, ObsEvento = ?
                WHERE IDRegistroStatus = ?
            """, (id_novo_motivo, obs_final, id_registro_status))

        # 3. Registrar no log de eventos (Opcional, mas bom para rastreio)
        cursor_local.execute("""
            INSERT INTO TBL_EventoStatus (IDMaquina, Status, DataHoraEvento, IDMotivoParada, ObsEvento) 
            SELECT IDMaquina, 0, GETDATE(), ?, ? FROM TBL_StatusMaquina WHERE IDRegistroStatus = ?
        """, (id_novo_motivo, f'Histórico alterado: {obs_final}', id_registro_status))

        conn_local.commit()
        return jsonify({'success': True, 'message': 'Parada reclassificada com sucesso!'})

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao reclassificar parada anterior: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Erro interno no servidor.'}), 500
    finally:
        if conn_local: devolver_conexao(conn_local)

@app.route('/api/paradas_pendentes/<int:id_maquina>')
@login_requerido
def api_paradas_pendentes(id_maquina):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # ----- INÍCIO DA ALTERAÇÃO -----
        tempo_max_classificacao = obter_configuracao('TEMPO_MAXIMO_CLASSIFICACAO_PARADA_MIN', conn_local, cursor_local)
        minutos_para_query = int(tempo_max_classificacao or 30)
        
        query_sql = """
            SELECT
                IDRegistroStatus,
                DataHoraInicio,
                DataHoraFim,
                DATEDIFF(SECOND, DataHoraInicio, DataHoraFim) as DuracaoSegundos
            FROM TBL_StatusMaquina
            WHERE IDMaquina = ?
              AND IDMotivoParada = 2 -- Parada Não Identificada
              AND DataHoraFim >= DATEADD(minute, ?, GETDATE())
            ORDER BY DataHoraFim DESC
        """
        cursor_local.execute(query_sql, (id_maquina, -minutos_para_query))
        # ----- FIM DA ALTERAÇÃO -----
        
        paradas = []
        for row in cursor_local.fetchall():
            paradas.append({
                'id_registro_status': row.IDRegistroStatus,
                'inicio': row.DataHoraInicio.strftime('%H:%M:%S'),
                'fim': row.DataHoraFim.strftime('%H:%M:%S'),
                'duracao': formatar_segundos_para_hms(row.DuracaoSegundos)
            })
            
        return jsonify({'success': True, 'paradas': paradas})

    except Exception as e:
        logger.error(f"Erro ao buscar paradas pendentes: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Erro ao buscar dados.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

            
# Em planner_app.py (pode ser perto de outras rotas de API)

@app.route('/api/materia_prima/<int:id_mp>/detalhes')
@login_requerido
def api_detalhes_materia_prima(id_mp):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        cursor_local.execute("""
            SELECT IDUnidade
            FROM TBL_MateriaPrima
            WHERE IDMateriaPrima = ?
        """, (id_mp,))
        materia_prima = cursor_local.fetchone()
        if materia_prima and materia_prima.IDUnidade:
            return jsonify({'success': True, 'id_unidade': materia_prima.IDUnidade})
        else:
            return jsonify({'success': False, 'message': 'Matéria-prima ou unidade padrão não encontrada.'}), 404
    except Exception as e:
        logger.error(f"Erro ao buscar detalhes da matéria-prima: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Erro interno no servidor.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)    

# Em planner_app.py

@app.route('/saida_materia_prima', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/saida_materia_prima')
def saida_materia_prima():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Busca a configuração ANTES de qualquer lógica
        usa_unidade_padrao_mp = obter_configuracao('USA_UNIDADE_PADRAO_MP', conn_local, cursor_local) == 'true'

        if request.method == 'POST':
            id_materia_prima = request.form.get('id_materia_prima')
            quantidade_saida_str = request.form.get('quantidade_saida', '0').replace(',', '.')
            quantidade_saida = float(quantidade_saida_str)
            data_retirada_str = request.form.get('data_retirada')
            nome_usuario_retirada = request.form.get('nome_usuario_retirada')
            destino = request.form.get('destino')
            ordem_vinculada = request.form.get('ordem_vinculada') or None
            observacao = request.form.get('observacao')

            id_unidade_medida = None
            # --- INÍCIO DA LÓGICA DE DECISÃO ---
            if usa_unidade_padrao_mp:
                # Se a configuração está ativa, busca a unidade do banco de dados
                cursor_local.execute("SELECT IDUnidade FROM TBL_MateriaPrima WHERE IDMateriaPrima = ?", id_materia_prima)
                unidade_row = cursor_local.fetchone()
                if unidade_row:
                    id_unidade_medida = unidade_row.IDUnidade
            else:
                # Se não, pega a unidade que o usuário selecionou no formulário
                id_unidade_medida = request.form.get('id_unidade_medida')
            # --- FIM DA LÓGICA DE DECISÃO ---

            if not all([id_materia_prima, quantidade_saida > 0, id_unidade_medida, nome_usuario_retirada, destino]):
                flash("Os campos Matéria-Prima, Quantidade, Unidade, Quem Retira e Destino são obrigatórios.", "error")
                return redirect(url_for('saida_materia_prima'))

            cursor_local.execute("SELECT NomeMateriaPrima FROM TBL_MateriaPrima WHERE IDMateriaPrima = ?", id_materia_prima)
            nome_materia_prima = cursor_local.fetchone().NomeMateriaPrima

            lotes_disponiveis = cursor_local.execute("""
                SELECT IDEstoque, QuantidadeDisponivel, Lote, IDFornecedor, NumeroNotaFiscal
                FROM TBL_EstoqueMP WITH (UPDLOCK)
                WHERE IDMateriaPrima = ? AND QuantidadeDisponivel > 0
                ORDER BY DataEntrada ASC
            """, (id_materia_prima,)).fetchall()

            estoque_total_disponivel = sum(float(l.QuantidadeDisponivel) for l in lotes_disponiveis)
            if estoque_total_disponivel < quantidade_saida:
                flash(f"Erro: Estoque insuficiente para '{nome_materia_prima}'. Solicitado: {quantidade_saida}, Disponível: {estoque_total_disponivel}", "error")
                return redirect(url_for('saida_materia_prima'))

            quantidade_restante_a_consumir = quantidade_saida
            for lote in lotes_disponiveis:
                if quantidade_restante_a_consumir <= 0: break

                consumo_deste_lote = min(quantidade_restante_a_consumir, float(lote.QuantidadeDisponivel))
                nova_quantidade = float(lote.QuantidadeDisponivel) - consumo_deste_lote

                cursor_local.execute(
                    "UPDATE TBL_EstoqueMP SET QuantidadeDisponivel = ? WHERE IDEstoque = ?",
                    (nova_quantidade, lote.IDEstoque)
                )

                data_selecionada = datetime.strptime(data_retirada_str, '%Y-%m-%d').date()
                hora_atual = datetime.now().time()
                data_hora_evento_log = datetime.combine(data_selecionada, hora_atual)
                
                obs_final = f"Destino: {destino}. Obs: {observacao or 'N/A'}"
                cursor_local.execute("""
                    INSERT INTO TBL_LogMovimentacaoEstoque 
                    (DataHoraEvento, IDEstoqueMP, IDMateriaPrima, Lote, TipoMovimento, Quantidade, IDUsuario, 
                     NomeUsuarioRetirada, Destino, Observacao, OrdemVinculada, IDFornecedor, NumeroNotaFiscal)
                    VALUES (?, ?, ?, ?, 'SAIDA_MANUAL_MP', ?, ?, ?, ?, ?, ?, ?, ?)
                """, (data_hora_evento_log, lote.IDEstoque, id_materia_prima, lote.Lote, -consumo_deste_lote, 
                      session.get('usuario_id'), nome_usuario_retirada, destino, obs_final, ordem_vinculada, 
                      lote.IDFornecedor, lote.NumeroNotaFiscal))
                
                quantidade_restante_a_consumir -= consumo_deste_lote

            conn_local.commit()
            flash(f"Saída de {quantidade_saida} de '{nome_materia_prima}' registada com sucesso!", "success")
            return redirect(url_for('saida_materia_prima'))

        # Lógica GET
        cursor_local.execute("SELECT IDMateriaPrima, NomeMateriaPrima, IDUnidade FROM TBL_MateriaPrima WHERE Ativo = 1 ORDER BY NomeMateriaPrima")
        materias_primas = cursor_local.fetchall()
        
        cursor_local.execute("SELECT IDUnidade, Sigla, NomeUnidade FROM TBL_UnidadeMedida")
        unidades_medida = cursor_local.fetchall()
        
        return render_template('saida_materia_prima.html', 
                               materias_primas=materias_primas,
                               unidades_medida=unidades_medida,
                               datetime=datetime,
                               usa_unidade_padrao_mp=usa_unidade_padrao_mp) # <-- Passa a configuração para o template

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em /saida_materia_prima: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar a página de saída de matéria-prima.", "error")
        return redirect(url_for('estoque_dashboard'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)            
            

############################################################## MODULO QUALIDADE ######################################################################

@app.route('/cadastros_qualidade')
@login_requerido
@permissao_requerida('/cadastros_qualidade') # Lembre-se de cadastrar esta permissão
def cadastros_qualidade():
    return render_template('cadastros_qualidade.html')
    
@app.route('/consulta_caracteristicas_qualidade')
@login_requerido
@permissao_requerida('/consulta_caracteristicas_qualidade') # Lembre-se de cadastrar esta permissão
def consulta_caracteristicas_qualidade():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        cursor_local.execute("""
            SELECT C.*, U.Sigla 
            FROM TBL_CaracteristicaQualidade C
            LEFT JOIN TBL_UnidadeMedida U ON C.IDUnidadeMedida = U.IDUnidade
            ORDER BY C.Nome
        """)
        caracteristicas = cursor_local.fetchall()
        
        return render_template('consulta_caracteristicas.html', caracteristicas=caracteristicas)

    except Exception as e:
        logger.error(f"Erro em /consulta_caracteristicas_qualidade: {e}", exc_info=True)
        flash("Ocorreu um erro ao carregar o catálogo de características.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)


@app.route('/cadastro_caracteristica_qualidade/', defaults={'id_caracteristica': None}, methods=['GET', 'POST'])
@app.route('/cadastro_caracteristica_qualidade/<int:id_caracteristica>', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_caracteristica_qualidade')
def cadastro_caracteristica_qualidade(id_caracteristica):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            id_caracteristica_form = request.form.get('id_caracteristica')
            codigo = request.form.get('codigo')
            nome = request.form.get('nome')
            descricao = request.form.get('descricao')
            tipo_dado = request.form.get('tipo_dado')
            id_unidade = request.form.get('id_unidade_medida')
            id_unidade = id_unidade if id_unidade else None # Converte string vazia para None
            ativo = 1 if 'ativo' in request.form else 0
            
            # Lógica de Upload de Imagem
            nome_arquivo_imagem = request.form.get('imagem_atual', None)
            if 'imagem_instrucao' in request.files:
                file = request.files['imagem_instrucao']
                if file.filename != '':
                    nome_arquivo_imagem = secure_filename(file.filename)
                    caminho_salvar = os.path.join(app.config['UPLOAD_FOLDER_INSTRUCOES'], nome_arquivo_imagem)
                    file.save(caminho_salvar)
            
            if id_caracteristica_form: # Atualização
                cursor_local.execute("""
                    UPDATE TBL_CaracteristicaQualidade SET
                    Codigo = ?, Nome = ?, Descricao = ?, TipoDado = ?, IDUnidadeMedida = ?, CaminhoImagemInstrucao = ?, Ativo = ?
                    WHERE IDCaracteristica = ?
                """, (codigo, nome, descricao, tipo_dado, id_unidade, nome_arquivo_imagem, ativo, id_caracteristica_form))
                flash("Característica atualizada com sucesso!", "success")
            else: # Novo Cadastro
                cursor_local.execute("""
                    INSERT INTO TBL_CaracteristicaQualidade 
                    (Codigo, Nome, Descricao, TipoDado, IDUnidadeMedida, CaminhoImagemInstrucao, Ativo)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                """, (codigo, nome, descricao, tipo_dado, id_unidade, nome_arquivo_imagem, ativo))
                flash("Característica cadastrada com sucesso!", "success")

            conn_local.commit()
            return redirect(url_for('consulta_caracteristicas_qualidade'))

        # Lógica GET
        caracteristica_para_editar = None
        if id_caracteristica:
            cursor_local.execute("SELECT * FROM TBL_CaracteristicaQualidade WHERE IDCaracteristica = ?", id_caracteristica)
            caracteristica_para_editar = cursor_local.fetchone()

        cursor_local.execute("SELECT IDUnidade, Sigla, NomeUnidade FROM TBL_UnidadeMedida WHERE Ativo = 1 ORDER BY NomeUnidade")
        unidades = cursor_local.fetchall()

        return render_template('cadastro_caracteristica.html', 
                               caracteristica=caracteristica_para_editar,
                               unidades=unidades)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em /cadastro_caracteristica_qualidade: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar o formulário da característica.", "error")
        return redirect(url_for('consulta_caracteristicas_qualidade'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)      
# Adicione esta rota para a CONSULTA de Planos de Inspeção
@app.route('/consulta_planos_inspecao')
@login_requerido
@permissao_requerida('/consulta_planos_inspecao') # Lembre-se de cadastrar esta permissão
def consulta_planos_inspecao():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # Query para buscar os planos e os nomes do produto/recurso associados
        cursor_local.execute("""
            SELECT 
                PI.*,
                P.NomeProduto,
                R.NomeMaquina
            FROM TBL_PlanoInspecao PI
            LEFT JOIN TBL_Produto P ON PI.IDProduto = P.IDProduto
            LEFT JOIN TBL_Recurso R ON PI.IDRecurso = R.IDMaquina
            ORDER BY PI.NomePlano
        """)
        planos = cursor_local.fetchall()
        
        return render_template('consulta_planos_inspecao.html', planos=planos)

    except Exception as e:
        logger.error(f"Erro em /consulta_planos_inspecao: {e}", exc_info=True)
        flash("Ocorreu um erro ao carregar a página de Planos de Inspeção.", "error")
        return redirect(url_for('modelagem')) # Redireciona para a modelagem em caso de erro
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# Adicione esta rota para o CADASTRO e EDIÇÃO de Planos de Inspeção
@app.route('/cadastro_plano_inspecao/', defaults={'id_plano': None}, methods=['GET', 'POST'])
@app.route('/cadastro_plano_inspecao/<int:id_plano>', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_plano_inspecao')
def cadastro_plano_inspecao(id_plano):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # --- LÓGICA POST (SALVAR DADOS) ---
        if request.method == 'POST':
            # Se a ação for adicionar uma característica
            if 'adicionar_caracteristica' in request.form:
                id_plano_form = request.form.get('id_plano')
                id_caracteristica_form = request.form.get('id_caracteristica')
                # Adicione aqui os outros campos do form de adicionar característica
                limite_minimo = request.form.get('limite_minimo') or None
                limite_maximo = request.form.get('limite_maximo') or None
                valor_nominal = request.form.get('valor_nominal') or None
                exibir_tolerancia = 1 if 'exibir_tolerancia' in request.form else 0

                cursor_local.execute("""
                    INSERT INTO TBL_PlanoInspecao_Caracteristicas
                    (IDPlanoInspecao, IDCaracteristica, LimiteMinimo, LimiteMaximo, ValorNominal, ExibirToleranciaOperador)
                    VALUES (?, ?, ?, ?, ?, ?)
                """, (id_plano_form, id_caracteristica_form, limite_minimo, limite_maximo, valor_nominal, exibir_tolerancia))
                conn_local.commit()
                flash("Característica adicionada ao plano com sucesso!", "success")
                return redirect(url_for('cadastro_plano_inspecao', id_plano=id_plano_form))
            
            # Se a ação for salvar o plano principal
            else:
                id_plano_form = request.form.get('id_plano')
                nome_plano = request.form.get('nome_plano')
                id_produto = request.form.get('id_produto') or None
                id_recurso = request.form.get('id_recurso') or None
                trigger_tipo = request.form.get('trigger_tipo')
                trigger_valor = request.form.get('trigger_valor') or None
                ativo = 1 if 'ativo' in request.form else 0

                if id_plano_form: # ATUALIZAÇÃO
                    cursor_local.execute("""
                        UPDATE TBL_PlanoInspecao SET
                        NomePlano = ?, IDProduto = ?, IDRecurso = ?, TriggerTipo = ?, TriggerValor = ?, Ativo = ?
                        WHERE IDPlanoInspecao = ?
                    """, (nome_plano, id_produto, id_recurso, trigger_tipo, trigger_valor, ativo, id_plano_form))
                    flash("Plano de Inspeção atualizado com sucesso!", "success")
                    id_plano_redirect = id_plano_form
                else: # CADASTRO
                    cursor_local.execute("""
                        INSERT INTO TBL_PlanoInspecao (NomePlano, IDProduto, IDRecurso, TriggerTipo, TriggerValor, Ativo)
                        OUTPUT INSERTED.IDPlanoInspecao
                        VALUES (?, ?, ?, ?, ?, ?)
                    """, (nome_plano, id_produto, id_recurso, trigger_tipo, trigger_valor, ativo))
                    id_plano_redirect = cursor_local.fetchone()[0]
                    flash("Plano de Inspeção cadastrado com sucesso! Agora adicione as características.", "success")
                
                conn_local.commit()
                return redirect(url_for('cadastro_plano_inspecao', id_plano=id_plano_redirect))

        # --- LÓGICA GET (EXIBIR PÁGINA) ---
        plano_para_editar = None
        caracteristicas_do_plano = []
        if id_plano:
            cursor_local.execute("SELECT * FROM TBL_PlanoInspecao WHERE IDPlanoInspecao = ?", id_plano)
            plano_para_editar = cursor_local.fetchone()
            
            # Busca as características já associadas a este plano
            cursor_local.execute("""
                SELECT PIC.*, C.Nome, C.TipoDado, UM.Sigla 
                FROM TBL_PlanoInspecao_Caracteristicas PIC
                JOIN TBL_CaracteristicaQualidade C ON PIC.IDCaracteristica = C.IDCaracteristica
                LEFT JOIN TBL_UnidadeMedida UM ON C.IDUnidadeMedida = UM.IDUnidade
                WHERE PIC.IDPlanoInspecao = ?
            """, id_plano)
            caracteristicas_do_plano = cursor_local.fetchall()

        # Busca dados para preencher os dropdowns do formulário
        cursor_local.execute("SELECT IDProduto, NomeProduto FROM TBL_Produto WHERE Habilitado = 1 ORDER BY NomeProduto")
        produtos = cursor_local.fetchall()
        cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina")
        recursos = cursor_local.fetchall()
        cursor_local.execute("SELECT IDCaracteristica, Nome, TipoDado FROM TBL_CaracteristicaQualidade WHERE Ativo = 1 ORDER BY Nome")
        caracteristicas_disponiveis = cursor_local.fetchall()

        return render_template('cadastro_plano_inspecao.html',
                               plano=plano_para_editar,
                               produtos=produtos,
                               recursos=recursos,
                               caracteristicas_disponiveis=caracteristicas_disponiveis,
                               caracteristicas_do_plano=caracteristicas_do_plano)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em /cadastro_plano_inspecao: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar o formulário do Plano de Inspeção.", "error")
        return redirect(url_for('consulta_planos_inspecao'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# Adicione esta rota para REMOVER uma característica de um plano
@app.route('/plano_inspecao/remover_caracteristica/<int:id_plano_caracteristica>', methods=['POST'])
@login_requerido
@permissao_requerida('/cadastro_plano_inspecao')
def remover_caracteristica_plano(id_plano_caracteristica):
    conn_local = None
    id_plano = request.form.get('id_plano') # Pega o ID do plano para redirecionar de volta
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        cursor_local.execute("DELETE FROM TBL_PlanoInspecao_Caracteristicas WHERE IDPlanoCaracteristica = ?", (id_plano_caracteristica,))
        conn_local.commit()
        flash("Característica removida do plano com sucesso.", "success")
    except Exception as e:
        if conn_local: conn_local.rollback()
        flash("Erro ao remover característica.", "error")
    finally:
        if conn_local: devolver_conexao(conn_local)
        
    return redirect(url_for('cadastro_plano_inspecao', id_plano=id_plano)) 

# Substitua a rota /api/checklist_inspecao/<int:id_maquina> por esta:
@app.route('/api/checklist_inspecao/<int:id_plano>')
@login_requerido
def api_checklist_inspecao(id_plano):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Busca o nome do plano
        cursor_local.execute("SELECT NomePlano FROM TBL_PlanoInspecao WHERE IDPlanoInspecao = ?", (id_plano,))
        plano = cursor_local.fetchone()
        if not plano:
            return jsonify({'success': False, 'message': 'Plano de Inspeção não encontrado.'})

        # Busca as características do plano (o checklist)
        cursor_local.execute("""
            SELECT 
                C.Nome, C.TipoDado, C.CaminhoImagemInstrucao,
                PIC.IDPlanoCaracteristica, PIC.LimiteMinimo, PIC.LimiteMaximo, PIC.ValorNominal, PIC.ExibirToleranciaOperador,
                UM.Sigla
            FROM TBL_PlanoInspecao_Caracteristicas PIC
            JOIN TBL_CaracteristicaQualidade C ON PIC.IDCaracteristica = C.IDCaracteristica
            LEFT JOIN TBL_UnidadeMedida UM ON C.IDUnidadeMedida = UM.IDUnidade
            WHERE PIC.IDPlanoInspecao = ?
        """, (id_plano,))
        
        checklist = [dict(zip([column[0] for column in cursor_local.description], row)) for row in cursor_local.fetchall()]

        return jsonify({
            'success': True,
            'id_plano': id_plano,
            'nome_plano': plano.NomePlano,
            'checklist': checklist
        })

    except Exception as e:
        logger.error(f"Erro em /api/checklist_inspecao: {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Erro interno no servidor.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
# Em planner_app.py, substitua a função api_verificar_inspecoes_pendentes por esta:

@app.route('/api/verificar_inspecoes_pendentes', methods=['POST'])
@login_requerido
def api_verificar_inspecoes_pendentes():
    conn_local = None
    try:
        data = request.json
        resultado = {} 

        ids_maquinas_raw = data.get('ids_maquinas', [])
        if not ids_maquinas_raw:
             return jsonify(resultado)

        try:
             ids_maquinas = [int(id_str) for id_str in ids_maquinas_raw] 
        except ValueError:
             logger.error(f"Erro ao converter IDs de máquina para int: {ids_maquinas_raw}")
             return jsonify({'error': 'IDs de máquina inválidos.'}), 400
        
        if not ids_maquinas:
            return jsonify(resultado)

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        placeholders = ','.join('?' for _ in ids_maquinas)
        cursor_local.execute(f"""
            SELECT IDMaquina, IDExecucao 
            FROM TBL_ExecucaoOP 
            WHERE Status IN ('Em Execucao', 'Em Setup')
              AND IDMaquina IN ({placeholders})
        """, ids_maquinas)
        execucoes_ativas_map = {row.IDMaquina: row.IDExecucao for row in cursor_local.fetchall()}

        for id_maq in ids_maquinas:
            resultado[id_maq] = []

        # 1. Busca os planos MANUAIS (com lógica de cooldown)
        cursor_local.execute("""
            SELECT IDPlanoInspecao, NomePlano, TriggerValor 
            FROM TBL_PlanoInspecao 
            WHERE Ativo = 1 AND TriggerTipo = 'MANUAL'
        """)
        planos_manuais = cursor_local.fetchall()
        
        map_exec_para_checar = list(execucoes_ativas_map.values())
        ultimas_inspecoes_manuais = {}
        if map_exec_para_checar:
            placeholders_exec_cooldown = ','.join('?' for _ in map_exec_para_checar)
            
            # ===== INÍCIO DA CORREÇÃO (DataHoraInspecao e execute) =====
            # Esta query agora usa a coluna correta que você mencionou.
            cursor_local.execute(f"""
                SELECT IDPlanoInspecao, IDExecucaoOP, MAX(DataHoraInspecao) as UltimaVez
                FROM TBL_RegistroInspecao
                WHERE IDExecucaoOP IN ({placeholders_exec_cooldown})
                GROUP BY IDPlanoInspecao, IDExecucaoOP
            """, map_exec_para_checar)
            # ===== FIM DA CORREÇÃO =====
            
            for reg in cursor_local.fetchall():
                ultimas_inspecoes_manuais[(reg.IDPlanoInspecao, reg.IDExecucaoOP)] = reg.UltimaVez

        for id_maq, id_execucao_ativa in execucoes_ativas_map.items():
            for plano_m in planos_manuais:
                em_cooldown = False
                cooldown_minutos = float(plano_m.TriggerValor or 0)
                
                if cooldown_minutos > 0:
                    chave = (plano_m.IDPlanoInspecao, id_execucao_ativa)
                    ultima_vez = ultimas_inspecoes_manuais.get(chave)
                    
                    if ultima_vez:
                        minutos_desde_ultima = (datetime.now() - ultima_vez).total_seconds() / 60.0
                        if minutos_desde_ultima < cooldown_minutos:
                            em_cooldown = True # Ainda está em cooldown
                
                if not em_cooldown:
                    resultado[id_maq].append({
                        'id_plano': plano_m.IDPlanoInspecao,
                        'nome_plano': plano_m.NomePlano,
                        'tipo': 'manual',
                        'id_inspecao_pendente': None,
                        'qtd_pendentes': 1 
                    })
        
        # 2. Lógica de agrupamento (sem alteração)
        if execucoes_ativas_map:
            ids_execucao_ativas = list(execucoes_ativas_map.values())
            placeholders_exec = ','.join('?' for _ in ids_execucao_ativas)
            
            # ===== INÍCIO DA CORREÇÃO (execute) =====
            cursor_local.execute(f"""
                SELECT 
                    MIN(P.IDInspecaoPendente) as IDInspecaoPendente, -- Pega a mais antiga
                    COUNT(*) as QtdPendentes,
                    P.IDExecucaoOP, 
                    PI.NomePlano, 
                    PI.IDPlanoInspecao
                FROM TBL_InspecaoPendente P
                JOIN TBL_PlanoInspecao PI ON P.IDPlanoInspecao = PI.IDPlanoInspecao
                WHERE P.Status = 'Pendente'
                  AND P.IDExecucaoOP IN ({placeholders_exec})
                GROUP BY P.IDExecucaoOP, PI.NomePlano, PI.IDPlanoInspecao
            """, ids_execucao_ativas)
            # ===== FIM DA CORREÇÃO =====
            
            pendencias_agrupadas = cursor_local.fetchall()
            
            map_exec_to_maq = {v: k for k, v in execucoes_ativas_map.items()}

            for pend in pendencias_agrupadas:
                id_maq_correspondente = map_exec_to_maq.get(pend.IDExecucaoOP)
                if id_maq_correspondente:
                    resultado[id_maq_correspondente].append({
                        'id_plano': pend.IDPlanoInspecao,
                        'nome_plano': pend.NomePlano,
                        'tipo': 'automatico',
                        'id_inspecao_pendente': pend.IDInspecaoPendente,
                        'qtd_pendentes': pend.QtdPendentes
                    })

        return jsonify(resultado)

    except Exception as e:
        logger.error(f"Erro em /api/verificar_inspecoes_pendentes (lógica de agrupamento): {e}", exc_info=True)
        return jsonify({'error': 'Erro interno no servidor'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
@app.route('/salvar_inspecao', methods=['POST'])
@login_requerido
def salvar_inspecao():
    conn_local = None
    try:
        data = request.form
        
        id_plano = data.get('id_plano_inspecao')
        id_inspecao_pendente = data.get('id_inspecao_pendente') # Pode ser '', 'None', ou '345'
        id_maquina = data.get('id_maquina_inspecao')
        observacao = data.get('observacao_inspecao')
        id_usuario_logado = session.get('usuario_id') 

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # 1. Busca informações do Plano
        cursor_local.execute("SELECT NomePlano, BloqueiaMaquinaEmCasoDeReprovacao FROM TBL_PlanoInspecao WHERE IDPlanoInspecao = ?", (id_plano,))
        plano_info = cursor_local.fetchone()
        if not plano_info:
            return jsonify({'success': False, 'message': 'Plano de Inspeção não encontrado.'}), 404

        # 2. Encontra a execução de OP ativa
        cursor_local.execute("SELECT TOP 1 IDExecucao FROM TBL_ExecucaoOP WHERE IDMaquina = ? AND Status IN ('Em Execucao', 'Em Setup')", (id_maquina,))
        execucao = cursor_local.fetchone()
        if not execucao:
            return jsonify({'success': False, 'message': 'Nenhuma OP em execução encontrada para registrar a inspeção.'}), 400

        # 3. Processa os resultados
        status_geral = 'APROVADO'
        resultados_processados = []
        for key, value in data.items():
            if key.startswith('resultado_'):
                id_plano_caracteristica = key.split('_')[1]
                
                cursor_local.execute("SELECT * FROM TBL_PlanoInspecao_Caracteristicas WHERE IDPlanoCaracteristica = ?", (id_plano_caracteristica,))
                plano_carac = cursor_local.fetchone()

                tipo_dado = data.get(f'tipo_dado_{id_plano_caracteristica}')
                status_item = 'APROVADO'
                
                valor_medido_numerico = None
                valor_medido_texto = None

                if tipo_dado == 'NUMERICO':
                    valor_medido_texto = value 
                    try:
                        valor_medido = float(str(value).replace(',', '.')) 
                        valor_medido_numerico = valor_medido 
                        limite_min = float(plano_carac.LimiteMinimo) if plano_carac.LimiteMinimo is not None else None
                        limite_max = float(plano_carac.LimiteMaximo) if plano_carac.LimiteMaximo is not None else None
                        
                        if (limite_min is not None and valor_medido < limite_min) or \
                           (limite_max is not None and valor_medido > limite_max):
                            status_item = 'REPROVADO'
                    except (ValueError, TypeError):
                        status_item = 'REPROVADO' 
                        
                else: # VISUAL
                    valor_medido_texto = value
                    if value != 'APROVADO':
                        status_item = 'REPROVADO'
                
                if status_item == 'REPROVADO':
                    status_geral = 'REPROVADO'
                
                resultados_processados.append({
                    'id_plano_caracteristica': id_plano_caracteristica,
                    'resultado_numerico': valor_medido_numerico,
                    'resultado_texto': valor_medido_texto,
                    'status': status_item
                })
        
        # 4. Insere o cabeçalho do registro de inspeção
        # (Usando a coluna DataHoraInspecao que você confirmou)
        cursor_local.execute("""
            INSERT INTO TBL_RegistroInspecao (IDPlanoInspecao, IDExecucaoOP, IDOperador, StatusGeral, Observacao, DataHoraInspecao)
            OUTPUT INSERTED.IDRegistroInspecao
            VALUES (?, ?, ?, ?, ?, GETDATE())
        """, (id_plano, execucao.IDExecucao, id_usuario_logado, status_geral, observacao))
        id_registro_inspecao = cursor_local.fetchone()[0]

        # 5. Insere os resultados detalhados
        for res in resultados_processados:
            cursor_local.execute("""
                INSERT INTO TBL_RegistroInspecao_Resultados
                (IDRegistroInspecao, IDPlanoCaracteristica, ResultadoNumerico, ResultadoTexto, StatusResultado)
                VALUES (?, ?, ?, ?, ?)
            """, (id_registro_inspecao, res['id_plano_caracteristica'], res['resultado_numerico'], res['resultado_texto'], res['status']))

        # --- INÍCIO DA CORREÇÃO DO BUG (V2.4 - SIMPLIFICADA) ---
        
        # Tenta converter o ID que veio do formulário
        try:
            id_pendente_int = int(id_inspecao_pendente)
        except (ValueError, TypeError):
            id_pendente_int = None # Se for '' ou 'None', vira None

        # Se tivermos um ID de pendência válido (NÃO sendo uma inspeção manual)...
        if id_pendente_int is not None:
            logger.info(f"Fechando inspeção pendente ID: {id_pendente_int}")
            
            # REMOVEMOS A QUERY COMPLEXA QUE ESTAVA CAUSANDO O ERRO.
            # Esta é a única query necessária.
            cursor_local.execute("""
                UPDATE TBL_InspecaoPendente 
                SET Status = 'Concluida', 
                    DataConclusao = GETDATE(), 
                    IDRegistroInspecao = ?
                WHERE IDInspecaoPendente = ?
            """, (id_registro_inspecao, id_pendente_int))
            
        # --- FIM DA CORREÇÃO DO BUG (V2.4) ---

        # 6. Lógica de Bloqueio (se reprovado)
        if status_geral == 'REPROVADO' and plano_info.BloqueiaMaquinaEmCasoDeReprovacao:
            logger.warning(f"Inspeção {id_registro_inspecao} reprovada! Bloqueando máquina {id_maquina} conforme plano '{plano_info.NomePlano}'.")
            
            cursor_local.execute("SELECT IDMotivoParada FROM TBL_MotivoParada WHERE Codigo = 'QLD'")
            motivo_qualidade = cursor_local.fetchone()
            
            if motivo_qualidade:
                id_motivo_parada_qualidade = motivo_qualidade.IDMotivoParada
                _update_machine_status(
                    conn_local, 
                    cursor_local, 
                    int(id_maquina), 
                    new_status=0,
                    id_motivo_parada=id_motivo_parada_qualidade, 
                    obs_evento=f"Reprovada na Inspeção: {plano_info.NomePlano}"
                )
            else:
                logger.error("Não foi possível bloquear a máquina por qualidade: Motivo de parada com Codigo 'QLD' não encontrado.")

        conn_local.commit()
        return jsonify({'success': True}) # O JavaScript cuidará da mensagem de sucesso

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em /salvar_inspecao (V2.4): {e}", exc_info=True)
        return jsonify({'success': False, 'message': 'Erro interno ao salvar a inspeção.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
            
            ##############SETUP################
@app.route('/iniciar_setup', methods=['POST'])
@login_requerido
@permissao_requerida('/iniciar_setup')
def iniciar_setup():
    conn_local = None
    try:
        id_ordem = request.form['id_ordem']
        id_maquina = request.form['id_maquina']
        
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("SELECT TOP 1 IDExecucao FROM TBL_ExecucaoOP WHERE IDMaquina = ? AND Status IN ('Em Execucao', 'Em Setup')", (id_maquina,))
        if cursor_local.fetchone():
            return jsonify({'status': 'error', 'message': 'Máquina já possui uma OP em execução ou em setup.'}), 409

        cursor_local.execute("SELECT IDStatus FROM TBL_StatusOrdemProducao WHERE NomeStatus = 'Em Setup'")
        status_setup_row = cursor_local.fetchone()
        ID_STATUS_EM_SETUP = status_setup_row.IDStatus if status_setup_row else 6

        cursor_local.execute("SELECT IDMotivoParada FROM TBL_MotivoParada WHERE Codigo = '03'")
        motivo_setup = cursor_local.fetchone()
        if not motivo_setup:
            return jsonify({'status': 'error', 'message': "Motivo de parada 'SETUP' não encontrado."}), 500
        id_motivo_setup = motivo_setup.IDMotivoParada

        cursor_local.execute("""
            SELECT RP.TempoSetupSegundos
            FROM TBL_OrdemProducao OP
            JOIN TBL_RecursoProduto RP ON OP.IDProduto = RP.IDProduto AND RP.IDRecurso = ?
            WHERE OP.IDOrdem = ?
        """, (id_maquina, id_ordem))
        config_setup = cursor_local.fetchone()
        
        # ===== CORREÇÃO AQUI: Convertendo Decimal para Float =====
        tempo_setup_segundos = float(config_setup.TempoSetupSegundos) if config_setup and config_setup.TempoSetupSegundos is not None else 0.0
        # =========================================================

        id_usuario_logado = session.get('usuario_id')
        cursor_local.execute("SELECT IDOperador FROM TBL_Operador WHERE IDUsuario = ? AND Ativo = 1", id_usuario_logado)
        operador_logado = cursor_local.fetchone()
        id_operador_correto = operador_logado.IDOperador if operador_logado else None

        id_turno = identificar_turno(conn_local, cursor_local)
        
        cursor_local.execute("""
            INSERT INTO TBL_ExecucaoOP (IDOrdem, IDMaquina, IDOperador, IDTurno, DataHoraInicio, Status, IDStatus)
            VALUES (?, ?, ?, ?, GETDATE(), 'Em Setup', ?)
        """, (id_ordem, id_maquina, id_operador_correto, id_turno, ID_STATUS_EM_SETUP))
        
        cursor_local.execute("UPDATE TBL_OrdemProducao SET IDStatus = ? WHERE IDOrdem = ?", (ID_STATUS_EM_SETUP, id_ordem))
        cursor_local.execute("DELETE FROM TBL_FilaOrdem WHERE IDOrdem = ? AND IDMaquina = ?", (id_ordem, id_maquina))

        id_registro_status_setup = _update_machine_status(
            conn_local, cursor_local, int(id_maquina), 0,
            id_motivo_parada=id_motivo_setup,
            obs_evento='Início do setup para OP'
        )

        if id_registro_status_setup and tempo_setup_segundos > 0:
            # Passa o valor float convertido
            agendar_verificacao_estouro_setup(int(id_maquina), id_registro_status_setup, tempo_setup_segundos)

        conn_local.commit()
        return jsonify({'status': 'success', 'message': 'Setup iniciado com sucesso! O tempo já está sendo monitorado.'})

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao iniciar setup: {e}", exc_info=True)
        return jsonify({'status': 'error', 'message': f'Ocorreu um erro no servidor: {e}'}), 500
    finally:
        if conn_local: devolver_conexao(conn_local)
            
@app.route('/relatorio_rastreabilidade_pa', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relatorio_rastreabilidade_pa') # Lembre-se de criar esta permissão no sistema
def relatorio_rastreabilidade_pa():
    conn_local = None
    resultados = []
    
    # Define filtros com datas padrão para os últimos 7 dias
    filtros = {
        "data_inicio": request.form.get("data_inicio", (datetime.now() - timedelta(days=7)).strftime('%Y-m-%d')),
        "data_fim": request.form.get("data_fim", datetime.now().strftime('%Y-m-%d')),
        "lote_pa": request.form.get("lote_pa", "")
    }

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            # A query principal que conecta todas as informações
            query = """
                SELECT
                    LogSaidaPA.IDLog AS IDSaida,
                    LogSaidaPA.DataHoraEvento AS DataSaida,
                    P_PA.NomeProduto,
                    LogSaidaPA.Lote AS LotePA,
                    ABS(LogSaidaPA.Quantidade) AS QuantidadeSaida,
                    LogSaidaPA.Observacao AS InfoSaida, -- Contém Destino e Documento
                    OP.CodigoOrdem,
                    R.NomeMaquina AS Recurso,
                    MP.NomeMateriaPrima,
                    LogConsumoMP.Lote AS LoteMP,
                    ABS(LogConsumoMP.Quantidade) AS QuantidadeConsumidaMP
                FROM
                    TBL_LogMovimentacaoEstoque AS LogSaidaPA
                JOIN TBL_Produto P_PA ON LogSaidaPA.IDProduto = P_PA.IDProduto
                -- O Lote do PA é o Código da Ordem de Produção
                JOIN TBL_OrdemProducao OP ON LogSaidaPA.Lote = OP.CodigoOrdem
                -- Encontra as execuções daquela ordem
                JOIN TBL_ExecucaoOP EX ON OP.IDOrdem = EX.IDOrdem
                -- Encontra o recurso (máquina) da execução
                JOIN TBL_Recurso R ON EX.IDMaquina = R.IDMaquina
                -- Encontra os LOGS de consumo de MP para aquela execução
                JOIN TBL_LogMovimentacaoEstoque AS LogConsumoMP ON EX.IDExecucao = LogConsumoMP.IDExecucaoOP AND LogConsumoMP.TipoMovimento = 'CONSUMO_PRODUCAO'
                -- Encontra os dados da Matéria-Prima consumida
                JOIN TBL_MateriaPrima MP ON LogConsumoMP.IDMateriaPrima = MP.IDMateriaPrima
                WHERE
                    LogSaidaPA.TipoMovimento = 'SAIDA_EXPEDICAO'
            """
            params = []

            # Adiciona os filtros à query
            if filtros["data_inicio"]:
                query += " AND CAST(LogSaidaPA.DataHoraEvento AS DATE) >= ?"
                params.append(filtros["data_inicio"])
            if filtros["data_fim"]:
                query += " AND CAST(LogSaidaPA.DataHoraEvento AS DATE) <= ?"
                params.append(filtros["data_fim"])
            if filtros["lote_pa"]:
                query += " AND LogSaidaPA.Lote LIKE ?"
                params.append(f"%{filtros['lote_pa']}%")
            
            query += " ORDER BY DataSaida DESC, LotePA, NomeMateriaPrima"
            
            cursor_local.execute(query, params)
            
            # Agrupa os resultados em Python para uma exibição mais clara
            resultados_agrupados = defaultdict(lambda: {'info_saida': None, 'consumo_mp': []})
            for row in cursor_local.fetchall():
                chave = row.IDSaida
                if not resultados_agrupados[chave]['info_saida']:
                    resultados_agrupados[chave]['info_saida'] = {
                        'DataSaida': row.DataSaida,
                        'NomeProduto': row.NomeProduto,
                        'LotePA': row.LotePA,
                        'QuantidadeSaida': row.QuantidadeSaida,
                        'InfoSaida': row.InfoSaida,
                        'OrdemProduzida': row.CodigoOrdem,
                        'Recurso': row.Recurso
                    }
                resultados_agrupados[chave]['consumo_mp'].append({
                    'NomeMateriaPrima': row.NomeMateriaPrima,
                    'LoteMP': row.LoteMP,
                    'QuantidadeConsumidaMP': row.QuantidadeConsumidaMP
                })
            
            resultados = list(resultados_agrupados.values())

        return render_template("relatorio_rastreabilidade_pa.html",
                               resultados=resultados,
                               filtros=filtros)
    except Exception as e:
        logger.error(f"Erro em relatorio_rastreabilidade_pa: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerar o relatório de rastreabilidade.", "error")
        return redirect(url_for('relatorios')) # Altere para sua página principal de relatórios
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
# Adicione esta nova rota ao seu planner_app.py

@app.route('/api/dashboard/maquina/<int:id_maquina>')
@login_requerido
def api_update_dashboard_maquina(id_maquina):
    conn_local = None
    try:
        conn_local = obter_conexao()
        
        # Lógica para buscar o status atual
        with conn_local.cursor() as cursor_local:
            cursor_local.execute("""
                SELECT TOP 1 Status, ObsEvento FROM TBL_StatusMaquina
                WHERE IDMaquina = ? AND DataHoraFim IS NULL ORDER BY DataHoraRegistro DESC
            """, (id_maquina,))
            status_row = cursor_local.fetchone()
        
        # Lógica para buscar o nome do turno atual
        nome_turno_maquina = "Fora de Turno"
        with conn_local.cursor() as cursor_local:
            id_turno_maquina = identificar_turno_da_maquina(conn_local, cursor_local, id_maquina)
            if id_turno_maquina:
                cursor_local.execute("SELECT NomeTurno FROM TBL_Turno WHERE IDTurno = ?", id_turno_maquina)
                turno_row = cursor_local.fetchone()
                if turno_row:
                    nome_turno_maquina = turno_row.NomeTurno
        
        # Prepara os dados para enviar de volta como JSON
        dados_atualizados = {
            'status_id': status_row.Status if status_row else -1,
            'status_descricao': status_row.ObsEvento if status_row and status_row.ObsEvento else "Sem Status",
            'nome_turno': nome_turno_maquina
        }
        
        return jsonify(dados_atualizados)

    except Exception as e:
        logger.error(f"Erro na API de atualização do dashboard para máquina {id_maquina}: {e}", exc_info=True)
        return jsonify({'error': 'Falha ao buscar dados'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)            
            
# Em planner_app.py, substitua esta função inteira:

def gerar_inspecoes_pendentes_thread():
    """
    [VERSÃO 2.3 - CORREÇÃO DO INSERT DE RESET]
    Remove a coluna 'DataHoraInspecao' que não existe na TBL_InspecaoPendente
    ao salvar o registro de 'RESETADO'.
    """
    logger.info("Thread do Robô de Inspeções Pendentes (V2.3 - Com Reset de Checkpoint) iniciada.")
    while True:
        conn_thread = None
        try:
            conn_thread = conectar_bd()
            cursor_thread = conn_thread.cursor()

            # --- ETAPA 1: Busca OPs Ativas ---
            cursor_thread.execute("""
                SELECT 
                    E.IDExecucao, E.IDMaquina, O.IDProduto,
                    DATEDIFF(SECOND, E.DataHoraInicio, GETDATE()) as TempoDecorridoSeg,
                    ISNULL((SELECT SUM(Quantidade) FROM VW_EventoProducaoComCicloReal WITH (NOLOCK)
                            WHERE IDExecucao = E.IDExecucao AND TipoValor IN ('BOA', 'ESTORNO')), 0) as TotalProduzido
                FROM TBL_ExecucaoOP E
                JOIN TBL_OrdemProducao O ON E.IDOrdem = O.IDOrdem
                WHERE E.Status IN ('Em Execucao', 'Em Setup')
            """)
            execucoes_ativas = cursor_thread.fetchall()
            # --- FIM ETAPA 1 ---

            for execucao in execucoes_ativas:
                id_execucao = execucao.IDExecucao
                
                try:
                    # 2. Busca os planos aplicáveis
                    cursor_thread.execute("""
                        SELECT IDPlanoInspecao, NomePlano, TriggerTipo, TriggerValor
                        FROM TBL_PlanoInspecao
                        WHERE Ativo = 1 
                          AND (IDProduto = ? OR IDRecurso = ? OR (IDProduto IS NULL AND IDRecurso IS NULL))
                          AND TriggerTipo <> 'MANUAL'
                    """, (execucao.IDProduto, execucao.IDMaquina))
                    
                    planos_aplicaveis = cursor_thread.fetchall()

                    for plano in planos_aplicaveis:
                        id_plano = plano.IDPlanoInspecao
                        trigger_valor_float = float(plano.TriggerValor or 0)
                        
                        # Valores atuais da execução
                        current_prod = float(execucao.TotalProduzido or 0)
                        current_time_min = (execucao.TempoDecorridoSeg or 0) / 60.0

                        # 3. Busca o Checkpoint (a "memória")
                        cursor_thread.execute("""
                            SELECT 
                                MAX(CheckpointProducao) as LastCheckedProduction,
                                MAX(CheckpointTempoMin) as LastCheckedTimeMin,
                                COUNT(*) as QtdCriada
                            FROM TBL_InspecaoPendente 
                            WHERE IDExecucaoOP = ? AND IDPlanoInspecao = ?
                        """, (id_execucao, id_plano))
                        
                        checkpoint = cursor_thread.fetchone()
                        
                        last_prod = float(checkpoint.LastCheckedProduction or 0)
                        last_time_min = float(checkpoint.LastCheckedTimeMin or 0)
                        inspecoes_ja_criadas = checkpoint.QtdCriada or 0

                        # 4. Lógica de Cálculo de Delta (com correção de reset)
                        novo_checkpoint_prod = last_prod
                        novo_checkpoint_time_min = last_time_min
                        novas_pendencias = 0 # Inicializa como 0

                        if plano.TriggerTipo == 'INICIO_OP':
                            if inspecoes_ja_criadas == 0:
                                novas_pendencias = 1
                                # Checkpoint não é relevante para INICIO_OP
                        
                        elif plano.TriggerTipo == 'QUANTIDADE' and trigger_valor_float > 0:
                            delta_prod = current_prod - last_prod
                            if delta_prod >= trigger_valor_float:
                                calculadas = int(delta_prod // trigger_valor_float) 
                                
                                if calculadas > 1:
                                    novas_pendencias = 0 
                                    novo_checkpoint_prod = current_prod 
                                    logger.warning(f"Robô Qualidade (V-Reset): Catch-up de PRODUÇÃO detectado para Plano '{plano.NomePlano}' (OP {id_execucao}). Produção pulou de {last_prod} para {current_prod}. Resetando checkpoint para {current_prod} e ignorando {calculadas} pendências passadas.")
                                    
                                    # #############################################
                                    # ##          INÍCIO DA CORREÇÃO           ##
                                    # #############################################
                                    # REMOVIDA A COLUNA DataHoraInspecao DESTE INSERT
                                    cursor_thread.execute("""
                                        INSERT INTO TBL_InspecaoPendente 
                                        (IDPlanoInspecao, IDExecucaoOP, Status, CheckpointProducao, CheckpointTempoMin)
                                        VALUES (?, ?, 'RESETADO', ?, ?)
                                    """, (id_plano, id_execucao, novo_checkpoint_prod, None))
                                    # #############################################
                                    # ##           FIM DA CORREÇÃO             ##
                                    # #############################################
                                    conn_thread.commit() # Commita o reset
                                    
                                else:
                                    novas_pendencias = 1
                                    novo_checkpoint_prod = last_prod + (novas_pendencias * trigger_valor_float)

                        elif plano.TriggerTipo == 'TEMPO' and trigger_valor_float > 0:
                            delta_time = current_time_min - last_time_min
                            if delta_time >= trigger_valor_float:
                                calculadas = int(delta_time // trigger_valor_float)

                                if calculadas > 1:
                                    novas_pendencias = 0 
                                    novo_checkpoint_time_min = current_time_min
                                    logger.warning(f"Robô Qualidade (V-Reset): Catch-up de TEMPO detectado para Plano '{plano.NomePlano}' (OP {id_execucao}). Resetando checkpoint para {current_time_min}min e ignorando {calculadas} pendências passadas.")
                                    
                                    # #############################################
                                    # ##          INÍCIO DA CORREÇÃO           ##
                                    # #############################################
                                    # REMOVIDA A COLUNA DataHoraInspecao DESTE INSERT
                                    cursor_thread.execute("""
                                        INSERT INTO TBL_InspecaoPendente 
                                        (IDPlanoInspecao, IDExecucaoOP, Status, CheckpointProducao, CheckpointTempoMin)
                                        VALUES (?, ?, 'RESETADO', ?, ?)
                                    """, (id_plano, id_execucao, None, novo_checkpoint_time_min))
                                    # #############################################
                                    # ##           FIM DA CORREÇÃO             ##
                                    # #############################################
                                    conn_thread.commit() # Commita o reset
                                else:
                                    novas_pendencias = 1
                                    novo_checkpoint_time_min = last_time_min + (novas_pendencias * trigger_valor_float)
                        
                        # 5. Cria as pendências (SE novas_pendencias > 0)
                        if novas_pendencias > 0:
                            logger.info(f"Robô Qualidade (V-Reset): Gerando {novas_pendencias} pendência(s) (Normal) do plano '{plano.NomePlano}' para a OP {id_execucao}.")
                            
                            for i in range(novas_pendencias):
                                checkpoint_prod_desta_linha = None
                                checkpoint_time_desta_linha = None

                                if plano.TriggerTipo == 'QUANTIDADE':
                                    checkpoint_prod_desta_linha = novo_checkpoint_prod
                                elif plano.TriggerTipo == 'TEMPO':
                                    checkpoint_time_desta_linha = novo_checkpoint_time_min

                                cursor_thread.execute("""
                                    INSERT INTO TBL_InspecaoPendente 
                                    (IDPlanoInspecao, IDExecucaoOP, Status, CheckpointProducao, CheckpointTempoMin)
                                    VALUES (?, ?, 'Pendente', ?, ?)
                                """, (id_plano, id_execucao, checkpoint_prod_desta_linha, checkpoint_time_desta_linha))
                            
                            conn_thread.commit() # Commita a criação das pendências
                
                except Exception as e_op:
                    logger.error(f"Erro no Robô Qualidade (V-Reset) ao processar OP {id_execucao}: {e_op}", exc_info=True)
                    if conn_thread: conn_thread.rollback() 

        except Exception as e_main:
            logger.error(f"Erro CRÍTICO no thread do Robô de Inspeções Pendentes (V-Reset): {e_main}", exc_info=True)
            if conn_thread: conn_thread.rollback()
        finally:
            if conn_thread:
                devolver_conexao(conn_thread)
        
        time.sleep(30)
# Em planner_app.py (adicionar estas duas novas rotas)

@app.route('/relatorio_inspecoes', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relatorio_inspecoes') # Lembre-se de cadastrar esta permissão no sistema
def relatorio_inspecoes():
    conn_local = None
    resultados_agrupados = []
    
    # Define filtros com datas padrão
    filtros = {
        "data_inicio": request.form.get("data_inicio", (datetime.now() - timedelta(days=7)).strftime('%Y-%m-%d')),
        "data_fim": request.form.get("data_fim", datetime.now().strftime('%Y-%m-%d')),
        "id_maquina": request.form.get("id_maquina", ""),
        "id_produto": request.form.get("id_produto", ""),
        "id_usuario_inspetor": request.form.get("id_usuario_inspetor", ""),
        "status_geral": request.form.get("status_geral", "") # 'APROVADO', 'REPROVADO', ou ''
    }

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Busca dados para os filtros (sempre)
        maquinas = cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina").fetchall()
        produtos = cursor_local.execute("SELECT IDProduto, CodigoProduto, NomeProduto FROM TBL_Produto WHERE Habilitado = 1 ORDER BY NomeProduto").fetchall()
        inspetores = cursor_local.execute("SELECT IDUsuario, NomeUsuario FROM TBL_Usuario WHERE Ativo = 1 ORDER BY NomeUsuario").fetchall()
        
        status_lista = [
            {'valor': 'APROVADO', 'nome': 'Aprovado'},
            {'valor': 'REPROVADO', 'nome': 'Reprovado'}
        ]

        if request.method == 'POST':
            # Query complexa para buscar cabeçalhos e detalhes
            query = """
                SELECT 
                    RI.IDRegistroInspecao, RI.DataHoraInspecao, RI.StatusGeral, RI.Observacao AS ObsGeral,
                    PI.NomePlano,
                    OP.CodigoOrdem,
                    P.NomeProduto,
                    R.NomeMaquina,
                    U.NomeUsuario AS NomeInspetor,
                    C.Nome AS NomeCaracteristica,
                    C.TipoDado,
                    RR.ResultadoNumerico,
                    RR.ResultadoTexto,
                    RR.StatusResultado
                FROM TBL_RegistroInspecao RI
                JOIN TBL_PlanoInspecao PI ON RI.IDPlanoInspecao = PI.IDPlanoInspecao
                JOIN TBL_ExecucaoOP EX ON RI.IDExecucaoOP = EX.IDExecucao
                JOIN TBL_OrdemProducao OP ON EX.IDOrdem = OP.IDOrdem
                JOIN TBL_Produto P ON OP.IDProduto = P.IDProduto
                JOIN TBL_Recurso R ON EX.IDMaquina = R.IDMaquina
                LEFT JOIN TBL_Usuario U ON RI.IDOperador = U.IDUsuario
                LEFT JOIN TBL_RegistroInspecao_Resultados RR ON RI.IDRegistroInspecao = RR.IDRegistroInspecao
                LEFT JOIN TBL_PlanoInspecao_Caracteristicas PIC ON RR.IDPlanoCaracteristica = PIC.IDPlanoCaracteristica
                LEFT JOIN TBL_CaracteristicaQualidade C ON PIC.IDCaracteristica = C.IDCaracteristica
                WHERE 1=1
            """
            
            params = []
            
            try:
                 data_inicio_dt = datetime.strptime(filtros["data_inicio"], "%Y-%m-%d").replace(hour=0, minute=0, second=0)
                 data_fim_dt = datetime.strptime(filtros["data_fim"], "%Y-%m-%d").replace(hour=23, minute=59, second=59)
                 
                 query += " AND RI.DataHoraInspecao BETWEEN ? AND ?"
                 params.extend([data_inicio_dt, data_fim_dt])
            except ValueError:
                 flash("Formato de data inválido.", "warning")

            if filtros["id_maquina"]:
                query += " AND R.IDMaquina = ?"
                params.append(int(filtros["id_maquina"]))
            if filtros["id_produto"]:
                query += " AND P.IDProduto = ?"
                params.append(int(filtros["id_produto"]))
            if filtros["id_usuario_inspetor"]:
                query += " AND RI.IDOperador = ?"
                params.append(int(filtros["id_usuario_inspetor"]))
            if filtros["status_geral"]:
                query += " AND RI.StatusGeral = ?"
                params.append(filtros["status_geral"])
                
            query += " ORDER BY RI.DataHoraInspecao DESC, C.Nome ASC"
            
            cursor_local.execute(query, params)
            
            # Agrupar os resultados em Python
            resultados_dict = defaultdict(lambda: {'cabeçalho': None, 'detalhes': []})
            
            for row in cursor_local.fetchall():
                id_registro = row.IDRegistroInspecao
                if not resultados_dict[id_registro]['cabeçalho']:
                    resultados_dict[id_registro]['cabeçalho'] = {
                        'IDRegistroInspecao': row.IDRegistroInspecao,
                        'DataHoraInspecao': row.DataHoraInspecao.strftime('%d/%m/%Y %H:%M:%S'),
                        'StatusGeral': row.StatusGeral,
                        'ObsGeral': row.ObsGeral,
                        'NomePlano': row.NomePlano,
                        'CodigoOrdem': row.CodigoOrdem,
                        'NomeProduto': row.NomeProduto,
                        'NomeMaquina': row.NomeMaquina,
                        'NomeInspetor': row.NomeInspetor or 'N/A'
                    }
                
                # Adiciona o detalhe (se houver)
                if row.NomeCaracteristica:
                    resultados_dict[id_registro]['detalhes'].append({
                        'NomeCaracteristica': row.NomeCaracteristica,
                        'TipoDado': row.TipoDado,
                        'ResultadoNumerico': row.ResultadoNumerico,
                        'ResultadoTexto': row.ResultadoTexto,
                        'StatusResultado': row.StatusResultado
                    })

            resultados_agrupados = list(resultados_dict.values())
            
            if not resultados_agrupados:
                flash("Nenhuma inspeção encontrada para os filtros selecionados.", "info")

        return render_template("relatorio_inspecoes.html",
                               resultados=resultados_agrupados,
                               filtros=filtros,
                               maquinas=maquinas,
                               produtos=produtos,
                               inspetores=inspetores,
                               status_lista=status_lista)

    except Exception as e:
        logger.error(f"Erro em /relatorio_inspecoes: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerar o relatório de inspeções.", "error")
        return redirect(url_for('home')) # Ou para o hub de relatórios
    finally:
        if conn_local:
            devolver_conexao(conn_local)


@app.route('/relatorio_inspecoes/exportar', methods=['POST'])
@login_requerido
@permissao_requerida('/relatorio_inspecoes') # Reutiliza a permissão do relatório
def exportar_relatorio_inspecoes():
    conn_local = None
    try:
        # Recebe os filtros via JSON
        filtros = request.json
        if not filtros:
            return jsonify({"error": "Filtros não fornecidos"}), 400
            
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Query principal (mesma do relatório, mas sem paginação)
        query = """
            SELECT 
                RI.IDRegistroInspecao, 
                RI.DataHoraInspecao, 
                RI.StatusGeral, 
                RI.Observacao AS ObsGeral,
                PI.NomePlano,
                OP.CodigoOrdem,
                P.NomeProduto,
                R.NomeMaquina,
                U.NomeUsuario AS NomeInspetor,
                C.Nome AS NomeCaracteristica,
                C.TipoDado,
                RR.ResultadoNumerico,
                RR.ResultadoTexto,
                RR.StatusResultado
            FROM TBL_RegistroInspecao RI
            JOIN TBL_PlanoInspecao PI ON RI.IDPlanoInspecao = PI.IDPlanoInspecao
            JOIN TBL_ExecucaoOP EX ON RI.IDExecucaoOP = EX.IDExecucao
            JOIN TBL_OrdemProducao OP ON EX.IDOrdem = OP.IDOrdem
            JOIN TBL_Produto P ON OP.IDProduto = P.IDProduto
            JOIN TBL_Recurso R ON EX.IDMaquina = R.IDMaquina
            LEFT JOIN TBL_Usuario U ON RI.IDOperador = U.IDUsuario
            LEFT JOIN TBL_RegistroInspecao_Resultados RR ON RI.IDRegistroInspecao = RR.IDRegistroInspecao
            LEFT JOIN TBL_PlanoInspecao_Caracteristicas PIC ON RR.IDPlanoCaracteristica = PIC.IDPlanoCaracteristica
            LEFT JOIN TBL_CaracteristicaQualidade C ON PIC.IDCaracteristica = C.IDCaracteristica
            WHERE 1=1
        """
        
        params = []
        
        if filtros.get("data_inicio") and filtros.get("data_fim"):
            try:
                 data_inicio_dt = datetime.strptime(filtros["data_inicio"], "%Y-%m-%d").replace(hour=0, minute=0, second=0)
                 data_fim_dt = datetime.strptime(filtros["data_fim"], "%Y-%m-%d").replace(hour=23, minute=59, second=59)
                 query += " AND RI.DataHoraInspecao BETWEEN ? AND ?"
                 params.extend([data_inicio_dt, data_fim_dt])
            except ValueError:
                 pass # Ignora filtro de data se inválido

        if filtros.get("id_maquina"):
            query += " AND R.IDMaquina = ?"
            params.append(int(filtros["id_maquina"]))
        if filtros.get("id_produto"):
            query += " AND P.IDProduto = ?"
            params.append(int(filtros["id_produto"]))
        if filtros.get("id_usuario_inspetor"):
            query += " AND RI.IDOperador = ?"
            params.append(int(filtros["id_usuario_inspetor"]))
        if filtros.get("status_geral"):
            query += " AND RI.StatusGeral = ?"
            params.append(filtros["status_geral"])
            
        query += " ORDER BY RI.DataHoraInspecao DESC, C.Nome ASC"
        
        # Usar Pandas para ler o SQL e gerar o Excel
        df = pd.read_sql_query(query, conn_local, params=params)
        
        # Formatar os dados no DataFrame
        df['DataHoraInspecao'] = pd.to_datetime(df['DataHoraInspecao']).dt.strftime('%d/%m/%Y %H:%M:%S')
        df['ValorMedido'] = df.apply(
            lambda row: f"{row['ResultadoNumerico']:.3f}" if row['TipoDado'] == 'NUMERICO' and pd.notna(row['ResultadoNumerico']) else row['ResultadoTexto'], 
            axis=1
        )
        
        # Renomear colunas para o Excel
        df.rename(columns={
            'IDRegistroInspecao': 'ID Inspeção',
            'DataHoraInspecao': 'Data/Hora',
            'StatusGeral': 'Status Geral',
            'ObsGeral': 'Obs. Geral',
            'NomePlano': 'Plano de Inspeção',
            'CodigoOrdem': 'Ordem',
            'NomeProduto': 'Produto',
            'NomeMaquina': 'Máquina',
            'NomeInspetor': 'Inspetor',
            'NomeCaracteristica': 'Característica',
            'ValorMedido': 'Valor Medido',
            'StatusResultado': 'Status Item'
        }, inplace=True)
        
        # Selecionar e ordenar as colunas para o arquivo final
        colunas_finais = [
            'ID Inspeção', 'Data/Hora', 'Status Geral', 'NomePlano', 'Máquina', 'Ordem', 'Produto', 'Inspetor', 
            'Característica', 'Valor Medido', 'Status Item', 'Obs. Geral'
        ]
        df_final = df[colunas_finais]

        # Criar o arquivo Excel em memória
        output = io.BytesIO()
        with pd.ExcelWriter(output, engine='openpyxl') as writer:
            df_final.to_excel(writer, index=False, sheet_name='Relatorio_Inspecoes')
        output.seek(0)
        
        return send_file(
            output,
            mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
            as_attachment=True,
            download_name='relatorio_de_inspecoes.xlsx'
        )

    except Exception as e:
        logger.error(f"Erro ao exportar relatório de inspeções: {e}", exc_info=True)
        return jsonify({"error": "Falha ao gerar o arquivo Excel."}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)            
 ########################MQTT#############################

# 1. Crie o cliente MQTT como um objeto global e configure-o aqui.
#    Isso garante que haverá apenas UMA instância do cliente.
logger.info("Criando instância única do cliente MQTT.")
mqtt_client = mqtt.Client()

def on_connect(client, userdata, flags, rc):
    """Callback executado quando o cliente se conecta ao broker."""
    if rc == 0:
        logger.info(f"Conectado com sucesso ao broker MQTT.")
        # O tópico é assinado aqui, uma única vez por conexão bem-sucedida.
        topic = f"{FLASK_CLIENT_IDENTIFIER}/maq/#"
        client.subscribe(topic)
        logger.info(f"Assinado ao tópico: '{topic}'")
    else:
        logger.error(f"Falha na conexão MQTT, código de retorno: {rc}")

def on_message(client, userdata, msg):
    """Callback do MQTT (Produtor). Rápido, apenas coloca a mensagem na fila."""
    try:
        # A única responsabilidade é colocar a mensagem na fila para o outro thread processar.
        mqtt_message_queue.put(msg)
    except Exception as e:
        logger.error(f"Erro ao colocar mensagem MQTT na fila: {e}", exc_info=True)

# 2. Associe os callbacks ao cliente global.
mqtt_client.on_connect = on_connect
mqtt_client.on_message = on_message

# 3. Configure a reconexão automática (opcional, mas recomendado).
#    Tenta reconectar a cada 5 segundos, até 10 vezes.
mqtt_client.reconnect_delay_set(min_delay=1, max_delay=5)

@app.route('/registrar_pulso', methods=['POST'])
def registrar_pulso():
    conn_local = None
    id_maquina = None
    try:
        data = request.get_json()
        id_maquina = data.get('id_maquina')
        pulsos_recebidos = int(data.get('pulsos', 1))
        origem = data.get('origem', 'ESP32')

        if not id_maquina:
            return jsonify({"status": "error", "message": "ID da máquina não fornecido"}), 400

        current_time = datetime.now()
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # ***** NOVA VERIFICAÇÃO: É SENSORIZADO? *****
        cursor_local.execute("SELECT Automatico FROM TBL_Recurso WHERE IDMaquina = ?", id_maquina)
        recurso_info_sensor = cursor_local.fetchone()
        if recurso_info_sensor and recurso_info_sensor.Automatico == 0:
            logger.warning(f"Pulso recebido via HTTP para máquina {id_maquina} configurada como manual. Ignorando.")
            devolver_conexao(conn_local)
            conn_local = None
            return jsonify({"status": "ignored", "message": "Pulso ignorado, máquina configurada como manual."})
        # ***** FIM DA NOVA VERIFICAÇÃO *****

        # --- INÍCIO DAS VERIFICAÇÕES (Lógica original mantida) ---
        cursor_local.execute("""
            SELECT TOP 1 Status, IDMotivoParada
            FROM TBL_StatusMaquina
            WHERE IDMaquina = ? AND DataHoraFim IS NULL
            ORDER BY DataHoraRegistro DESC
        """, id_maquina)
        status_atual_row = cursor_local.fetchone()

        # ... (Restante da lógica original de verificação de status 'Fora de Turno' e 'RetornoAutomaticoProducao') ...
        if status_atual_row and status_atual_row.Status == 0:
            # 2. Verificar se o motivo é "Fora de Turno"
            if status_atual_row.IDMotivoParada == ID_MOTIVO_FORA_DE_TURNO:
                logger.info(f"Pulso ignorado para máquina {id_maquina}. Status atual é 'Fora de Turno'.")
                devolver_conexao(conn_local)
                conn_local = None
                return jsonify({"status": "ignored", "message": "Pulso ignorado, máquina fora de turno."})
            # 3. Se não for "Fora de Turno", verificar a flag RetornoAutomaticoProducao
            else:
                cursor_local.execute("""
                    SELECT TOP 1 MP.RetornoAutomaticoProducao
                    FROM TBL_StatusMaquina SM
                    JOIN TBL_MotivoParada MP ON SM.IDMotivoParada = MP.IDMotivoParada
                    WHERE SM.IDMaquina = ? AND SM.Status = 0 AND SM.DataHoraFim IS NULL
                      AND SM.IDRegistroStatus = (SELECT MAX(IDRegistroStatus) FROM TBL_StatusMaquina WHERE IDMaquina = ? AND DataHoraFim IS NULL)
                """, (id_maquina, id_maquina))
                motivo_parada_info = cursor_local.fetchone()

                if motivo_parada_info and not motivo_parada_info.RetornoAutomaticoProducao:
                     logger.info(f"Pulso ignorado para máquina {id_maquina}. Motivo de parada ID {status_atual_row.IDMotivoParada} não permite retorno automático.")
                     devolver_conexao(conn_local)
                     conn_local = None
                     return jsonify({"status": "ignored", "message": "Motivo de parada atual não permite retorno automático."})
        # --- FIM DAS VERIFICAÇÕES ---

        # ... (Restante da lógica de debounce, atualização de status e registro de produção continua igual) ...
        # Lógica de debounce
        cursor_local.execute("SELECT IntervaloDebounceSegundos FROM TBL_Recurso WHERE IDMaquina = ?", id_maquina)
        recurso_info = cursor_local.fetchone()
        intervalo_debounce = recurso_info.IntervaloDebounceSegundos if recurso_info else 0

        if intervalo_debounce > 0:
            with pulse_debounce_lock:
                last_ts = last_pulse_timestamps.get(id_maquina)
                if last_ts and (current_time - last_ts).total_seconds() < intervalo_debounce:
                    logger.debug(f"Pulso para máquina {id_maquina} ignorado devido ao debounce.")
                    devolver_conexao(conn_local)
                    conn_local = None
                    return jsonify({"status": "debounced", "message": "Pulso ignorado (debounce)."}), 200
                last_pulse_timestamps[id_maquina] = current_time

        _update_machine_status(conn_local, cursor_local, id_maquina, 1, obs_evento="Produção detectada via pulso")
        id_turno_atual = identificar_turno(conn_local, cursor_local)

        cursor_local.execute("""
            SELECT TOP 1 E.IDExecucao, O.IDOrdem, E.IDOperador, R.IDTipo, O.IDProduto, P.PulsosPorProducao,
                   E.IDOrdemOperacao,
                   CASE WHEN O.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.FatorMultiplicacao
                        ELSE P.FatorMultiplicacao END AS FatorMultiplicacaoFinal
            FROM TBL_ExecucaoOP E
            JOIN TBL_Recurso R ON R.IDMaquina = E.IDMaquina
            JOIN TBL_OrdemProducao O ON O.IDOrdem = E.IDOrdem
            JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
            LEFT JOIN TBL_RecursoProduto RP ON E.IDMaquina = RP.IDRecurso AND O.IDProduto = RP.IDProduto
            WHERE E.IDMaquina = ? AND E.Status = 'Em Execucao' ORDER BY E.DataHoraInicio DESC
        """, id_maquina)
        execucao_info = cursor_local.fetchone()

        if execucao_info:
            pulsos_para_um_ciclo = float(execucao_info.PulsosPorProducao or 1)
            pecas_por_ciclo = float(execucao_info.FatorMultiplicacaoFinal or 1)
            producao_a_registrar = (pulsos_recebidos / pulsos_para_um_ciclo) * pecas_por_ciclo

            cursor_local.execute("""
                INSERT INTO VW_EventoProducaoComCicloReal (
                    IDExecucao, IDTipoEvento, Quantidade, DataHoraEvento, IDMaquina, IDOrdemProducao,
                    IDTurno, IDOperador, TipoValor, OrigemEvento, IDTipoRecurso, IDOrdemOperacao
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, 'BOA', ?, ?, ?)
            """, (
                execucao_info.IDExecucao, 1, producao_a_registrar, current_time, id_maquina,
                execucao_info.IDOrdem, id_turno_atual, execucao_info.IDOperador, origem,
                execucao_info.IDTipo, execucao_info.IDOrdemOperacao
            ))
            message = "Evento de produção registrado."
        else:
            cursor_local.execute("""
                INSERT INTO VW_EventoProducaoComCicloReal (IDMaquina, IDTurno, Quantidade, DataHoraEvento, IDTipoEvento, TipoValor, OrigemEvento)
                VALUES (?, ?, 0, ?, 1, 'BOA', ?)
            """, (id_maquina, id_turno_atual, current_time, origem))
            message = "Pulso de atividade registrado (sem OP)."

        conn_local.commit()
        return jsonify({ "status": "success", "message": message })

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao registrar pulso: {str(e)}", exc_info=True)
        return jsonify({"status": "error", "message": str(e)}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

def mqtt_database_writer_thread():
    while True:
        try:
            # Tenta pegar uma mensagem da fila (aguarda até 0.5s)
            msg = mqtt_message_queue.get(timeout=0.5)
            
            conn_local = None
            try:
                conn_local = obter_conexao()
                cursor_local = conn_local.cursor()
                
                topic = msg.topic
                payload_str = msg.payload.decode('utf-8')
                
                # O tópico vem como: cliente/maq/ID/tipo
                # Ex: fabrica_edu_hml/maq/1/conexao
                partes_topico = topic.split('/')
                
                if len(partes_topico) >= 4 and partes_topico[1] == 'maq':
                    try:
                        id_maquina = int(partes_topico[2])
                        tipo_msg = partes_topico[3] # 'pulso', 'status', 'conexao'
                    except ValueError:
                        logger.error(f"ID da máquina inválido no tópico: {topic}")
                        continue

                    # === 1. LÓGICA DE CONEXÃO (ONLINE/OFFLINE + IP) ===
                    if tipo_msg == 'conexao':
                        timestamp_agora = datetime.now()
                        status_rede = 'offline' # Valor padrão
                        ip_atual = None

                        # Tenta ler como JSON para pegar o IP
                        try:
                            dados_conexao = json.loads(payload_str)
                            status_rede = dados_conexao.get('status', 'offline')
                            ip_atual = dados_conexao.get('ip')
                        except json.JSONDecodeError:
                            # Fallback: Se chegar mensagem antiga (texto puro), usa ela
                            status_rede = payload_str.lower()
                        
                        # Define status: 1 = Online, 0 = Offline
                        status_int = 1 if status_rede == 'online' else 0
                        
                        # Atualiza no Banco
                        if ip_atual:
                            cursor_local.execute("""
                                UPDATE TBL_DispositivoESP32 
                                SET UltimaConexao = ?, Status = ?, EnderecoIP = ?
                                WHERE IDMaquina = ?
                            """, (timestamp_agora, status_int, ip_atual, id_maquina))
                        else:
                            cursor_local.execute("""
                                UPDATE TBL_DispositivoESP32 
                                SET UltimaConexao = ?, Status = ?
                                WHERE IDMaquina = ?
                            """, (timestamp_agora, status_int, id_maquina))
                        
                        # Se não atualizou nada (máquina nova), insere
                        if cursor_local.rowcount == 0:
                            cursor_local.execute("""
                                INSERT INTO TBL_DispositivoESP32 (CodigoDispositivo, IDMaquina, UltimaConexao, Status, EnderecoIP)
                                VALUES (?, ?, ?, ?, ?)
                            """, (f"ESP32_Auto_{id_maquina}", id_maquina, timestamp_agora, status_int, ip_atual))

                        # Se for OFFLINE, registra histórico de queda
                        if status_rede == 'offline':
                            logger.warning(f"⚠️ Máquina {id_maquina} reportou OFFLINE. Registrando evento.")
                            cursor_local.execute("""
                                INSERT INTO TBL_EventoStatus (IDMaquina, Status, DataHoraEvento, ObsEvento) 
                                VALUES (?, 0, ?, 'Queda de Conexão (MQTT)')
                            """, (id_maquina, timestamp_agora))
                            
                        conn_local.commit()

                    # === 2. LÓGICA DE PULSO DE PRODUÇÃO ===
                    elif tipo_msg == 'pulso':
                        try:
                            data = json.loads(payload_str)
                            pulsos = int(data.get('pulsos', 1))
                            
                            # Registra pulso usando a lógica existente da API
                            # Aqui repetimos a lógica essencial para garantir performance sem chamar rota HTTP
                            
                            # A. Atualiza Status para Rodando
                            _update_machine_status(conn_local, cursor_local, id_maquina, 1, obs_evento="Produção via MQTT")
                            
                            # B. Identifica Turno e OP Ativa
                            id_turno = identificar_turno(conn_local, cursor_local)
                            current_time = datetime.now()
                            
                            cursor_local.execute("""
                                SELECT TOP 1 E.IDExecucao, O.IDOrdem, E.IDOperador, R.IDTipo, E.IDOrdemOperacao,
                                       P.PulsosPorProducao, 
                                       CASE WHEN O.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL 
                                            THEN RP.FatorMultiplicacao ELSE P.FatorMultiplicacao END AS Fator
                                FROM TBL_ExecucaoOP E
                                JOIN TBL_Recurso R ON R.IDMaquina = E.IDMaquina
                                JOIN TBL_OrdemProducao O ON O.IDOrdem = E.IDOrdem
                                JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
                                LEFT JOIN TBL_RecursoProduto RP ON E.IDMaquina = RP.IDRecurso AND O.IDProduto = RP.IDProduto
                                WHERE E.IDMaquina = ? AND E.Status = 'Em Execucao' 
                                ORDER BY E.DataHoraInicio DESC
                            """, (id_maquina,))
                            exec_info = cursor_local.fetchone()
                            
                            if exec_info:
                                div_pulsos = float(exec_info.PulsosPorProducao or 1)
                                fator = float(exec_info.Fator or 1)
                                qtd = (pulsos / div_pulsos) * fator
                                
                                cursor_local.execute("""
                                    INSERT INTO VW_EventoProducaoComCicloReal (
                                        IDExecucao, IDTipoEvento, Quantidade, DataHoraEvento, IDMaquina, 
                                        IDOrdemProducao, IDTurno, IDOperador, TipoValor, OrigemEvento, 
                                        IDTipoRecurso, IDOrdemOperacao
                                    ) VALUES (?, 1, ?, ?, ?, ?, ?, ?, 'BOA', 'MQTT', ?, ?)
                                """, (
                                    exec_info.IDExecucao, qtd, current_time, id_maquina,
                                    exec_info.IDOrdem, id_turno, exec_info.IDOperador,
                                    exec_info.IDTipo, exec_info.IDOrdemOperacao
                                ))
                                conn_local.commit()
                                logger.info(f"Pulso MQTT registrado para Maq {id_maquina}: {qtd} peça(s)")
                            
                        except json.JSONDecodeError:
                            logger.error(f"Erro JSON no pulso: {payload_str}")

                    # === 3. LÓGICA DE STATUS DA MÁQUINA (0 ou 1) ===
                    elif tipo_msg == 'status':
                        try:
                            data = json.loads(payload_str)
                            status_maq = int(data.get('status', 0)) # 1=Rodando, 0=Parada
                            
                            # Atualiza apenas se for diferente do atual para não flodar o banco
                            _update_machine_status(conn_local, cursor_local, id_maquina, status_maq, obs_evento="Status via MQTT")
                            conn_local.commit()
                        except Exception as e:
                            pass

            except Exception as e:
                if conn_local: conn_local.rollback()
                logger.error(f"Erro no thread de escrita do MQTT: {e}", exc_info=True)
            finally:
                if conn_local:
                    devolver_conexao(conn_local)

    # ESTES SÃO OS 'EXCEPT' QUE ESTAVAM FALTANDO NO SEU CÓDIGO:
        except queue.Empty:
            time.sleep(0.05) # Fila vazia, espera um pouco
        except Exception as e:
            logger.error(f"Erro crítico no loop MQTT: {e}", exc_info=True)
            time.sleep(1)
            
def mqtt_client_thread():
    """
    Thread que gerencia a conexão e o loop do cliente MQTT.
    Utiliza a instância global 'mqtt_client' e a lógica de reconexão da biblioteca.
    """
    mqtt_broker_address = "localhost"
    mqtt_port = 1883
    
    # --- INÍCIO DA CORREÇÃO ---
    # Garante que os callbacks estejam associados antes de conectar.
    # Embora já definidos globalmente, reforçar aqui torna o código mais robusto.
    mqtt_client.on_connect = on_connect
    mqtt_client.on_message = on_message
    # --- FIM DA CORREÇÃO ---
    
    logger.info("Thread do cliente MQTT iniciada. Tentando conectar...")
    try:
        # Conecta-se ao broker. O timeout de 60s é para manter a conexão viva.
        mqtt_client.connect(mqtt_broker_address, mqtt_port, 60)
        
        # loop_forever() é um loop bloqueante que lida com a comunicação
        # e a reconexão automaticamente (graças à configuração reconnect_delay_set).
        mqtt_client.loop_forever()
    except Exception as e:
        # Este erro só deve acontecer se a conexão inicial falhar de forma crítica.
        logger.critical(f"Não foi possível iniciar o loop do cliente MQTT: {e}", exc_info=True)   

def enviar_relatorio_fim_turno(id_turno_finalizado):
    """
    Busca o ÚLTIMO 'snapshot' de OEE do turno que acabou de finalizar e envia por e-mail.
    VERSÃO CORRIGIDA E ROBUSTA
    """
    conn_local = None
    if not id_turno_finalizado:
        logger.warning("Tentativa de enviar relatório de fim de turno com ID de turno inválido.")
        return

    logger.info(f"INICIANDO GERAÇÃO (SNAPSHOT) DO RELATÓRIO DE FIM DE TURNO PARA O TURNO ID: {id_turno_finalizado}...")

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        query_oee_turno = """
            WITH UltimoOEE_DoTurno AS (
                SELECT
                    oee.*,
                    r.NomeMaquina,
                    ROW_NUMBER() OVER(PARTITION BY oee.IDMaquina ORDER BY oee.DataHoraCalculo DESC) as rn
                FROM TBL_IndiceOEE AS oee
                JOIN TBL_Recurso AS r ON oee.IDMaquina = r.IDMaquina
                WHERE
                    oee.IDTurno = ? 
                    AND oee.DataHoraCalculo >= DATEADD(hour, -24, GETDATE())
            )
            SELECT
                NomeMaquina,
                CAST(Disponibilidade * 100 AS DECIMAL(6, 2)) AS Disponibilidade,
                CAST(Performance * 100 AS DECIMAL(6, 2)) AS Performance,
                CAST(Qualidade * 100 AS DECIMAL(6, 2)) AS Qualidade,
                CAST(OEE * 100 AS DECIMAL(6, 2)) AS OEE
            FROM UltimoOEE_DoTurno
            WHERE rn = 1
            ORDER BY NomeMaquina;
        """

        df_relatorio = pd.read_sql_query(query_oee_turno, conn_local, params=[id_turno_finalizado])

        if df_relatorio.empty:
            logger.info(f"Nenhum dado de OEE encontrado para o turno {id_turno_finalizado} nas últimas 24h. Relatório não será enviado.")
            cursor_local.execute("""
                UPDATE TBL_LogRelatorioTurno SET Status = 'CONCLUIDO_SEM_DADOS' 
                WHERE IDTurno = ? AND CAST(DataRelatorio AS DATE) = CAST(GETDATE() AS DATE) AND Status = 'ENVIANDO'
            """, (id_turno_finalizado,))
            conn_local.commit()
            return

        cursor_local.execute("SELECT NomeTurno FROM TBL_Turno WHERE IDTurno = ?", id_turno_finalizado)
        turno_info = cursor_local.fetchone()
        nome_turno = turno_info.NomeTurno if turno_info else f"Turno ID {id_turno_finalizado}"

        colunas_para_formatar = ['Disponibilidade', 'Performance', 'Qualidade', 'OEE']
        for coluna in colunas_para_formatar:
            df_relatorio[coluna] = df_relatorio[coluna].apply(lambda x: f"{int(round(float(x), 0))}%")

        cursor_local.execute("""
            SELECT DISTINCT U.Email
            FROM TBL_Usuario U
            JOIN TBL_GrupoUsuario G ON U.IDGrupo = G.IDGrupo
            WHERE G.RecebeRelatorioOEE = 1 AND U.Ativo = 1 AND U.Email IS NOT NULL AND U.Email <> ''
        """)
        destinatarios = [row.Email for row in cursor_local.fetchall()]
        
        if not destinatarios:
            logger.warning("Nenhum usuário encontrado para receber o relatório de OEE. E-mail não será enviado.")
            return
            
        config_keys = "('SMTP_HOST', 'SMTP_PORT', 'SMTP_USER', 'SMTP_PASSWORD', 'SMTP_USE_TLS', 'SMTP_SENDER_EMAIL', 'SMTP_SENDER_NAME')"
        cursor_local.execute(f"SELECT ChaveConfig, ValorConfig FROM TBL_Configuracao WHERE ChaveConfig IN {config_keys}")
        config = {row.ChaveConfig: row.ValorConfig for row in cursor_local.fetchall()}

        data_hoje = datetime.now().strftime('%d/%m/%Y')
        assunto = f"Relatório de OEE - Fim do {nome_turno} - {data_hoje}"

        # --- INÍCIO DA CORREÇÃO ---
        # Removido o "f" e usado o método .format() para mais segurança
        html_template = """
        <html>
            <head>
                <style>
                    body {{ font-family: Arial, sans-serif; }}
                    table {{ border-collapse: collapse; width: 90%; margin: 20px auto; }}
                    th, td {{ border: 1px solid #cccccc; text-align: center; padding: 10px; }}
                    th {{ background-color: #004a99; color: white; }}
                    tr:nth-child(even) {{ background-color: #f2f2f2; }}
                    h2 {{ color: #004a99; text-align: center; }}
                </style>
            </head>
            <body>
                <h2>Snapshot de OEE do {turno}</h2>
                <p style="font-size: 0.9em; text-align: center; color: #555;">Os valores abaixo representam o último índice registrado para cada máquina durante o turno.</p>
                {tabela_html}
                <p style="font-size: 0.8em; text-align: center; color: #777;">Este é um e-mail automático gerado pelo Sistema Planner.</p>
            </body>
        </html>
        """
        tabela_html = df_relatorio.to_html(index=False, border=0)
        html_body = html_template.format(turno=nome_turno, tabela_html=tabela_html)
        # --- FIM DA CORREÇÃO ---
        
        msg = MIMEMultipart()
        sender_name = config.get('SMTP_SENDER_NAME', 'Planner')
        sender_email = config.get('SMTP_SENDER_EMAIL')
        msg['From'] = formataddr((sender_name, sender_email))
        msg['To'] = ", ".join(destinatarios)
        msg['Subject'] = assunto
        msg.attach(MIMEText(html_body, 'html'))
        
        server = smtplib.SMTP(config.get('SMTP_HOST'), int(config.get('SMTP_PORT')))
        if config.get('SMTP_USE_TLS', 'false').lower() == 'true':
            server.starttls()
        server.login(config.get('SMTP_USER'), config.get('SMTP_PASSWORD'))
        server.sendmail(config.get('SMTP_SENDER_EMAIL'), destinatarios, msg.as_string())
        server.quit()
        
        logger.info(f"E-mail de fim de turno ({nome_turno}) enviado com sucesso para {len(destinatarios)} destinatário(s).")

        cursor_local.execute("""
            UPDATE TBL_LogRelatorioTurno SET Status = 'CONCLUIDO' 
            WHERE IDTurno = ? AND CAST(DataRelatorio AS DATE) = CAST(GETDATE() AS DATE) AND Status = 'ENVIANDO'
        """, (id_turno_finalizado,))
        conn_local.commit()

    except Exception as e:
        logger.error(f"ERRO ao gerar/enviar relatório de fim de turno: {e}", exc_info=True)
        if conn_local:
            try:
                cursor_local.execute("""
                    UPDATE TBL_LogRelatorioTurno SET Status = 'FALHA' 
                    WHERE IDTurno = ? AND CAST(DataRelatorio AS DATE) = CAST(GETDATE() AS DATE) AND Status = 'ENVIANDO'
                """, (id_turno_finalizado,))
                conn_local.commit()
            except Exception as e_log:
                logger.error(f"Não foi possível registrar a falha no log de relatórios: {e_log}")
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
@app.route('/alertas_ativos')
@login_requerido
def alertas_ativos():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Busca o grupo do usuário logado para verificar a permissão
        cursor_local.execute("""
            SELECT G.PodeReconhecerAlerta
            FROM TBL_Usuario U
            JOIN TBL_GrupoUsuario G ON U.IDGrupo = G.IDGrupo
            WHERE U.IDUsuario = ?
        """, (session.get('usuario_id'),))
        
        permissao_usuario = cursor_local.fetchone()
        pode_reconhecer = permissao_usuario.PodeReconhecerAlerta if permissao_usuario else False

        # Busca os alertas que ainda estão com o status 'ATIVO'
        cursor_local.execute("""
            SELECT
                L.IDLogAlarme,
                L.DataHoraOcorrencia,
                M.Nome AS NomeAlarme,
                R.NomeMaquina,
                L.Observacao
            FROM TBL_LogAlarmes L
            JOIN TBL_MotivoAlarme M ON L.IDMotivoAlarme = M.IDMotivoAlarme
            LEFT JOIN TBL_Recurso R ON L.IDMaquina = R.IDMaquina
            WHERE L.Status = 'ATIVO'
            ORDER BY L.DataHoraOcorrencia DESC
        """)
        alertas = cursor_local.fetchall()

        # Renderiza um novo template que iremos criar
        return render_template('alertas_ativos.html', alertas=alertas, pode_reconhecer=pode_reconhecer)

    except Exception as e:
        logger.error(f"Erro em /alertas_ativos: {e}", exc_info=True)
        flash("Ocorreu um erro ao carregar a página de alertas.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)


@app.route('/alertas/reconhecer/<int:id_log_alarme>', methods=['POST'])
@login_requerido
def reconhecer_alerta(id_log_alarme):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # Atualiza o status do alerta específico no banco de dados
        cursor_local.execute("""
            UPDATE TBL_LogAlarmes
            SET Status = 'RECONHECIDO',
                IDUsuarioReconhecimento = ?,
                DataHoraReconhecimento = GETDATE()
            WHERE IDLogAlarme = ? AND Status = 'ATIVO'
        """, (session.get('usuario_id'), id_log_alarme))
        
        conn_local.commit()
        flash("Alerta reconhecido com sucesso!", "success")
        
    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro ao reconhecer alerta: {e}", exc_info=True)
        flash("Ocorreu um erro ao processar a solicitação.", "error")
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
    return redirect(url_for('alertas_ativos'))    

@app.route('/api/roteiro_padrao/<int:id_produto>')
@login_requerido
def api_roteiro_padrao(id_produto):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # --- ATUALIZADO: Adicionado NomeDocumentoTecnico ---
        cursor_local.execute("""
            SELECT Sequencia, NumeroOperacao, Descricao, IDRecurso, TempoSetupMinutos, NomeDocumentoTecnico
            FROM TBL_RoteiroOperacao
            WHERE IDProduto = ?
            ORDER BY Sequencia
        """, (id_produto,))
        
        operacoes = [dict(zip([column[0] for column in cursor_local.description], row)) for row in cursor_local.fetchall()]
        
        return jsonify(operacoes)

    except Exception as e:
        logger.error(f"Erro na API de roteiro padrão: {e}", exc_info=True)
        return jsonify({"error": "Falha ao buscar roteiro"}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/selecionar_produto_roteiro')
@login_requerido
@permissao_requerida('/selecionar_produto_roteiro') # Lembre-se de criar esta permissão no seu sistema
def selecionar_produto_roteiro():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # Busca todos os produtos habilitados para o usuário selecionar
        cursor_local.execute("""
            SELECT IDProduto, CodigoProduto, NomeProduto 
            FROM TBL_Produto 
            WHERE Habilitado = 1 
            ORDER BY NomeProduto
        """)
        produtos = cursor_local.fetchall()
        
        return render_template('selecionar_produto_roteiro.html', produtos=produtos)

    except Exception as e:
        logger.error(f"Erro em /selecionar_produto_roteiro: {e}", exc_info=True)
        flash("Ocorreu um erro ao carregar a lista de produtos.", "error")
        return redirect(url_for('cadastro_producao'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)


@app.route('/roteiro_produto/<int:id_produto>', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/gerenciar_roteiro')
def gerenciar_roteiro(id_produto):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            id_roteiro_operacao = request.form.get('id_roteiro_operacao')
            sequencia = request.form.get('sequencia')
            numero_operacao = request.form.get('numero_operacao')
            descricao = request.form.get('descricao')
            id_recurso = request.form.get('id_recurso')
            tempo_setup = request.form.get('tempo_setup') or 0
            # --- NOVO CAMPO ---
            nome_documento = request.form.get('nome_documento').strip() or None

            if id_roteiro_operacao:
                 # --- ATUALIZADO ---
                 cursor_local.execute("""
                    UPDATE TBL_RoteiroOperacao SET Sequencia=?, NumeroOperacao=?, Descricao=?, IDRecurso=?, TempoSetupMinutos=?, NomeDocumentoTecnico=?
                    WHERE IDRoteiroOperacao = ?
                 """, (sequencia, numero_operacao, descricao, id_recurso, tempo_setup, nome_documento, id_roteiro_operacao))
                 flash("Operação do roteiro atualizada com sucesso!", "success")
            else:
                # --- ATUALIZADO ---
                cursor_local.execute("""
                    INSERT INTO TBL_RoteiroOperacao (IDProduto, Sequencia, NumeroOperacao, Descricao, IDRecurso, TempoSetupMinutos, NomeDocumentoTecnico)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                """, (id_produto, sequencia, numero_operacao, descricao, id_recurso, tempo_setup, nome_documento))
                flash("Operação adicionada ao roteiro com sucesso!", "success")

            conn_local.commit()
            return redirect(url_for('gerenciar_roteiro', id_produto=id_produto))

        # --- LÓGICA GET (sem alteração, pois os SELECT * já buscam a nova coluna) ---
        id_operacao_editar = request.args.get('id_operacao_editar')
        operacao_para_editar = None
        if id_operacao_editar:
            cursor_local.execute("SELECT * FROM TBL_RoteiroOperacao WHERE IDRoteiroOperacao = ?", id_operacao_editar)
            operacao_para_editar = cursor_local.fetchone()

        cursor_local.execute("SELECT * FROM TBL_Produto WHERE IDProduto = ?", id_produto)
        produto = cursor_local.fetchone()

        cursor_local.execute("""
            SELECT R.*, REC.NomeMaquina FROM TBL_RoteiroOperacao R
            LEFT JOIN TBL_Recurso REC ON R.IDRecurso = REC.IDMaquina
            WHERE R.IDProduto = ? ORDER BY R.Sequencia
        """, id_produto)
        operacoes_roteiro = cursor_local.fetchall()

        cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina")
        recursos = cursor_local.fetchall()

        return render_template('gerenciar_roteiro.html',
                               produto=produto,
                               operacoes=operacoes_roteiro,
                               recursos=recursos,
                               operacao_para_editar=operacao_para_editar)

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro em /roteiro_produto: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerenciar o roteiro.", "error")
        return redirect(url_for('selecionar_produto_roteiro'))
    finally:
        if conn_local: devolver_conexao(conn_local)

@app.route('/roteiro_produto/deletar_operacao/<int:id_operacao>', methods=['POST'])
@login_requerido
@permissao_requerida('/gerenciar_roteiro')
def deletar_operacao_roteiro(id_operacao):
    conn_local = None
    id_produto = request.form.get('id_produto')
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        cursor_local.execute("DELETE FROM TBL_RoteiroOperacao WHERE IDRoteiroOperacao = ?", (id_operacao,))
        conn_local.commit()
        flash("Operação removida do roteiro.", "success")
    except Exception as e:
        if conn_local: conn_local.rollback()
        flash("Erro ao remover operação.", "error")
    finally:
        if conn_local: devolver_conexao(conn_local)
    return redirect(url_for('gerenciar_roteiro', id_produto=id_produto))  

# Em planner_app.py

@app.route('/api/configuracao_recurso_produto/<int:id_produto>/<int:id_recurso>')
@login_requerido
def api_configuracao_recurso_produto(id_produto, id_recurso):
    """
    Retorna a configuração específica de Tempo de Ciclo, Fator de Multiplicação
    e TEMPO DE SETUP da tabela TBL_RecursoProduto.
    """
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # +++++ ATUALIZADO: Adicionado TempoSetupSegundos ao SELECT +++++
        cursor_local.execute("""
            SELECT TempoCicloPadraoSegundos, FatorMultiplicacao, TempoSetupSegundos
            FROM TBL_RecursoProduto
            WHERE IDProduto = ? AND IDRecurso = ?
        """, (id_produto, id_recurso))
        
        config = cursor_local.fetchone()
        
        if config:
            # +++++ ATUALIZADO: Converte setup de segundos para minutos para a tela +++++
            tempo_setup_min = (config.TempoSetupSegundos / 60) if config.TempoSetupSegundos is not None else 0
            
            return jsonify({
                'success': True,
                'tempo_ciclo_segundos': config.TempoCicloPadraoSegundos,
                'fator_multiplicacao': config.FatorMultiplicacao,
                'tempo_setup_minutos': tempo_setup_min
            })
        else:
            return jsonify({'success': False, 'message': 'Nenhuma configuração encontrada para esta combinação.'}), 404

    except Exception as e:
        logger.error(f"Erro na API de configuração recurso x produto: {e}", exc_info=True)
        return jsonify({"error": "Falha ao buscar configuração"}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
@app.route('/gantt_sequenciamento', methods=['GET'])
@login_requerido
@permissao_requerida('/relatorios') 
def gantt_sequenciamento():
    conn_local = None
    timeline_data = []
    
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        agora = datetime.now()
        # Define o início do histórico (ontem à meia-noite)
        ponto_inicial_historico = agora.replace(hour=0, minute=0, second=0, microsecond=0) - timedelta(days=1)

        cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina")
        maquinas = cursor_local.fetchall()

        for maquina in maquinas:
            # --- PASSO 1: BUSCAR HISTÓRICO E STATUS ATUAL (Até "Agora") ---
            query_historico = """
                SELECT 
                    SM.IDRegistroStatus, SM.DataHoraInicio, 
                    ISNULL(SM.DataHoraFim, GETDATE()) AS DataHoraFimCalculada,
                    TS.NomeStatus AS CategoriaStatus, SM.IDMotivoParada,
                    MP.Codigo AS CodigoMotivoParada, MP.Descricao AS DescricaoMotivoParada,
                    ExecInfo.CodigoOrdem, ExecInfo.NumeroOperacao, ExecInfo.DescricaoOperacao
                FROM TBL_StatusMaquina SM
                JOIN TBL_TipoStatus TS ON SM.Status = TS.Status
                LEFT JOIN TBL_MotivoParada MP ON SM.IDMotivoParada = MP.IDMotivoParada
                OUTER APPLY (
                    SELECT TOP 1 OP.CodigoOrdem, OPO.NumeroOperacao, OPO.Descricao AS DescricaoOperacao
                    FROM TBL_ExecucaoOP EX
                    JOIN TBL_OrdemProducao OP ON EX.IDOrdem = OP.IDOrdem
                    LEFT JOIN TBL_OrdemProducao_Operacoes OPO ON EX.IDOrdemOperacao = OPO.IDOrdemOperacao
                    WHERE EX.IDMaquina = SM.IDMaquina 
                      AND SM.DataHoraInicio >= EX.DataHoraInicio 
                      AND (SM.DataHoraInicio < EX.DataHoraFim OR EX.DataHoraFim IS NULL)
                    ORDER BY EX.DataHoraInicio DESC
                ) AS ExecInfo
                WHERE SM.IDMaquina = ? 
                  AND SM.DataHoraInicio < ? 
                  AND ISNULL(SM.DataHoraFim, GETDATE()) > ? 
                ORDER BY SM.DataHoraInicio ASC
            """
            cursor_local.execute(query_historico, (maquina.IDMaquina, agora, ponto_inicial_historico))
            historico_e_status_atual = cursor_local.fetchall()
            
            for status in historico_e_status_atual:
                inicio_real = max(status.DataHoraInicio, ponto_inicial_historico)
                fim_real = min(status.DataHoraFimCalculada, agora) 

                if fim_real <= inicio_real: continue

                tipo_barra, label_ordem, label_operacao = 'parada', "Status Desconhecido", ""
                
                if status.CategoriaStatus == 'Produzindo':
                    tipo_barra = 'ativa'
                    label_ordem = status.CodigoOrdem or "Produção"
                    label_operacao = f"({status.NumeroOperacao}) {status.DescricaoOperacao}" if status.NumeroOperacao else "Produção (Histórico)"
                else:
                    if status.IDMotivoParada == ID_MOTIVO_FORA_DE_TURNO:
                        tipo_barra, label_ordem = 'fora_de_turno', "Fora de Turno"
                    elif status.CodigoMotivoParada == '03': 
                        tipo_barra = 'setup'
                        label_ordem = status.CodigoOrdem or "Setup"
                        label_operacao = f"({status.NumeroOperacao}) {status.DescricaoOperacao} (Setup)" if status.NumeroOperacao else "Setup (Histórico)"
                    else: 
                        tipo_barra = 'parada'
                        label_ordem = status.DescricaoMotivoParada or "Parada Não Identificada"
                        label_operacao = f"OP: {status.CodigoOrdem}" if status.CodigoOrdem else ""

                timeline_data.append([
                    maquina.NomeMaquina, label_ordem, label_operacao,
                    inicio_real.isoformat(), fim_real.isoformat(), tipo_barra
                ])

            # --- PASSO 2: PROJETAR A OP ATUAL (EM EXECUÇÃO) ---
            cursor_local.execute("""
                SELECT TOP 1
                    EX.IDOrdemOperacao, O.CodigoOrdem, O.QuantidadePlanejada, 
                    O.DataFimPlanejada, 
                    OPO.NumeroOperacao, OPO.Descricao AS DescricaoOperacao,
                    CASE WHEN O.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.TempoCicloPadraoSegundos ELSE P.TempoCicloSegundos END AS TempoCicloFinal,
                    O.FatorMultiplicacaoOrdem AS FatorMultiplicacaoFinal,
                    ISNULL((SELECT SUM(ev.Quantidade) FROM VW_EventoProducaoComCicloReal ev JOIN TBL_ExecucaoOP ex_inner ON ev.IDExecucao = ex_inner.IDExecucao WHERE ex_inner.IDOrdemOperacao = EX.IDOrdemOperacao AND ev.TipoValor IN ('BOA', 'ESTORNO')), 0) as QtdProduzidaNaOperacao
                FROM TBL_ExecucaoOP EX
                JOIN TBL_OrdemProducao O ON EX.IDOrdem = O.IDOrdem 
                JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
                LEFT JOIN TBL_OrdemProducao_Operacoes OPO ON EX.IDOrdemOperacao = OPO.IDOrdemOperacao
                LEFT JOIN TBL_RecursoProduto RP ON O.IDProduto = RP.IDProduto AND EX.IDMaquina = RP.IDRecurso
                WHERE EX.IDMaquina = ? AND EX.Status = 'Em Execucao'
            """, (maquina.IDMaquina,))
            ordem_ativa = cursor_local.fetchone()
            
            tempo_corrente_maquina = agora 

            if ordem_ativa:
                qtd_produzida = float(ordem_ativa.QtdProduzidaNaOperacao or 0)
                qtd_planejada = float(ordem_ativa.QuantidadePlanejada or 0)
                qtd_restante = max(0, qtd_planejada - qtd_produzida)
                tempo_ciclo_seg = float(ordem_ativa.TempoCicloFinal or 0)
                fator = float(ordem_ativa.FatorMultiplicacaoFinal or 1)
                
                tempo_restante_seg = (qtd_restante * tempo_ciclo_seg) / fator if qtd_restante > 0 and tempo_ciclo_seg > 0 and fator > 0 else 0
                
                data_inicio_projetada = agora
                data_fim_projetada = agora + timedelta(seconds=tempo_restante_seg)
                data_fim_planejada_ordem = ordem_ativa.DataFimPlanejada 
                
                op_label_ativa = f"({ordem_ativa.NumeroOperacao}) {ordem_ativa.DescricaoOperacao}" if ordem_ativa.NumeroOperacao else ""
                codigo_ordem_label = ordem_ativa.CodigoOrdem
                
                tempo_corrente_maquina = data_fim_projetada

                # Lógica de cor para a OP atual (Verde se OK, Laranja se atrasada)
                if data_fim_planejada_ordem and data_fim_projetada > data_fim_planejada_ordem and data_inicio_projetada < data_fim_planejada_ordem:
                    # Divide a barra: Parte no prazo (verde), parte atrasada (laranja)
                    timeline_data.append([
                        maquina.NomeMaquina, codigo_ordem_label, f"{op_label_ativa} (Projetado)",
                        data_inicio_projetada.isoformat(), data_fim_planejada_ordem.isoformat(), 'ativa'
                    ])
                    timeline_data.append([
                        maquina.NomeMaquina, codigo_ordem_label, f"{op_label_ativa} (ATRASADO)",
                        data_fim_planejada_ordem.isoformat(), data_fim_projetada.isoformat(), 'atrasada'
                    ])
                elif data_fim_planejada_ordem and data_inicio_projetada >= data_fim_planejada_ordem:
                    # Já começa atrasada
                    timeline_data.append([
                        maquina.NomeMaquina, codigo_ordem_label, f"{op_label_ativa} (ATRASADO)",
                        data_inicio_projetada.isoformat(), data_fim_projetada.isoformat(), 'atrasada'
                    ])
                else:
                    # Tudo no prazo
                    timeline_data.append([
                        maquina.NomeMaquina, codigo_ordem_label, f"{op_label_ativa} (Projetado)",
                        data_inicio_projetada.isoformat(), data_fim_projetada.isoformat(), 'ativa'
                    ])

            # --- PASSO 3: PROJETAR A FILA ---
            query_fila = """
                SELECT 
                    o.CodigoOrdem, opo.TempoSetupPlanejadoMinutos, o.QuantidadePlanejada,
                    o.DataFimPlanejada, 
                    opo.NumeroOperacao, opo.Descricao AS DescricaoOperacao,
                    ISNULL((SELECT SUM(Quantidade) FROM VW_EventoProducaoComCicloReal WHERE IDOrdemProducao = o.IDOrdem AND TipoValor IN ('BOA', 'ESTORNO')), 0) as QuantidadeJaProduzidaNaOrdem,
                    CASE WHEN o.UsarTempoCicloRecurso = 1 AND rp.IDRecursoProduto IS NOT NULL THEN rp.TempoCicloPadraoSegundos ELSE p.TempoCicloSegundos END AS TempoCicloFinalSeg,
                    o.FatorMultiplicacaoOrdem AS FatorMultiplicacaoFinal
                FROM TBL_FilaOrdem f 
                JOIN TBL_OrdemProducao_Operacoes opo ON f.IDOrdemOperacao = opo.IDOrdemOperacao 
                JOIN TBL_OrdemProducao o ON opo.IDOrdem = o.IDOrdem 
                JOIN TBL_Produto p ON p.IDProduto = o.IDProduto 
                LEFT JOIN TBL_RecursoProduto rp ON o.IDProduto = rp.IDProduto AND opo.IDRecurso = rp.IDRecurso 
                WHERE f.IDMaquina = ? 
                ORDER BY f.OrdemFila, opo.Sequencia
            """
            cursor_local.execute(query_fila, (maquina.IDMaquina,))
            operacoes_fila = cursor_local.fetchall()

            for op in operacoes_fila:
                 setup_min = float(op.TempoSetupPlanejadoMinutos or 0)
                 tempo_ciclo_seg = float(op.TempoCicloFinalSeg or 0)
                 fator = float(op.FatorMultiplicacaoFinal or 1.0)
                 qtd_planejada_total = float(op.QuantidadePlanejada or 0)
                 qtd_ja_produzida_total = float(op.QuantidadeJaProduzidaNaOrdem or 0)
                 qtd_restante_a_produzir = max(0, qtd_planejada_total - qtd_ja_produzida_total)
                 
                 data_limite_op = op.DataFimPlanejada 

                 tempo_producao_min = 0.0
                 if tempo_ciclo_seg > 0 and fator > 0 and qtd_restante_a_produzir > 0:
                     tempo_producao_seg = (qtd_restante_a_produzir * tempo_ciclo_seg) / fator
                     tempo_producao_min = tempo_producao_seg / 60
                 
                 op_label_fila = f"({op.NumeroOperacao}) {op.DescricaoOperacao}" if op.NumeroOperacao else ""

                 # 1. Projeção do SETUP
                 if setup_min > 0:
                     data_inicio_setup = tempo_corrente_maquina
                     data_fim_setup = data_inicio_setup + timedelta(minutes=setup_min)
                     
                     tipo_barra_setup = 'setup'
                     if data_limite_op and data_fim_setup > data_limite_op:
                         tipo_barra_setup = 'setup_atrasada' # Amarelo com borda vermelha

                     timeline_data.append([
                        maquina.NomeMaquina, 
                        op.CodigoOrdem, 
                        f"{op_label_fila} (Setup)", 
                        data_inicio_setup.isoformat(), 
                        data_fim_setup.isoformat(), 
                        tipo_barra_setup
                     ])
                     tempo_corrente_maquina = data_fim_setup

                 # 2. Projeção da PRODUÇÃO
                 if tempo_producao_min > 0:
                     data_inicio_prod = tempo_corrente_maquina
                     data_fim_prod = data_inicio_prod + timedelta(minutes=tempo_producao_min)
                     
                     tipo_barra_prod = 'producao'
                     label_status = "(Previsto)"
                     
                     # Se a produção terminar DEPOIS do prazo
                     if data_limite_op and data_fim_prod > data_limite_op:
                         tipo_barra_prod = 'producao_atrasada' # Azul com borda laranja
                         label_status = "(ATRASO PREVISTO)"

                     timeline_data.append([
                        maquina.NomeMaquina, 
                        op.CodigoOrdem, 
                        f"{op_label_fila} {label_status}", 
                        data_inicio_prod.isoformat(), 
                        data_fim_prod.isoformat(), 
                        tipo_barra_prod
                     ])
                     tempo_corrente_maquina = data_fim_prod
        
        filtros_fixos = {"data_inicio": ponto_inicial_historico.strftime('%Y-%m-%d'), "data_fim": (agora + timedelta(days=7)).strftime('%Y-%m-%d')}
        return render_template('gantt_sequenciamento.html', gantt_data_json=json.dumps(timeline_data), filtros=filtros_fixos)

    except Exception as e:
        logger.error(f"Erro CRÍTICO em /gantt_sequenciamento: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerar o gráfico de Gantt.", "error")
        return redirect(url_for('dashboard'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

@app.route('/gantt_status_maquinas', methods=['GET'])
@login_requerido
@permissao_requerida('/relatorios')
def gantt_status_maquinas():
    conn_local = None
    try:
        data_filtro_str = request.args.get('data_filtro', datetime.now().strftime('%Y-%m-%d'))
        data_filtro = datetime.strptime(data_filtro_str, '%Y-%m-%d')
        
        data_inicio = data_filtro.replace(hour=0, minute=0, second=0)
        data_fim = data_filtro.replace(hour=23, minute=59, second=59)

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # +++++ INÍCIO DA ALTERAÇÃO NA QUERY +++++
        # Adicionamos um OUTER APPLY para buscar a OP que estava em execução
        # durante o período de tempo do status da máquina.
        query = """
            SELECT 
                R.NomeMaquina,
                COALESCE(MP.Descricao, TS.NomeStatus, 'N/A') AS MotivoOuStatus,
                TS.NomeStatus AS CategoriaStatus,
                SM.DataHoraInicio,
                ISNULL(SM.DataHoraFim, GETDATE()) AS DataHoraFim,
                ExecInfo.CodigoOrdem -- << NOVA COLUNA
            FROM TBL_StatusMaquina SM
            JOIN TBL_Recurso R ON SM.IDMaquina = R.IDMaquina
            JOIN TBL_TipoStatus TS ON SM.Status = TS.Status
            LEFT JOIN TBL_MotivoParada MP ON SM.IDMotivoParada = MP.IDMotivoParada
            OUTER APPLY (
                SELECT TOP 1 OP.CodigoOrdem
                FROM TBL_ExecucaoOP EX
                JOIN TBL_OrdemProducao OP ON EX.IDOrdem = OP.IDOrdem
                WHERE EX.IDMaquina = SM.IDMaquina 
                  AND SM.DataHoraInicio >= EX.DataHoraInicio 
                  AND (SM.DataHoraInicio < EX.DataHoraFim OR EX.DataHoraFim IS NULL)
                ORDER BY EX.DataHoraInicio DESC
            ) AS ExecInfo
            WHERE 
                (SM.DataHoraInicio BETWEEN ? AND ?) OR (SM.DataHoraFim BETWEEN ? AND ?) OR (SM.DataHoraInicio < ? AND SM.DataHoraFim IS NULL)
            ORDER BY R.NomeMaquina, SM.DataHoraInicio
        """
        # +++++ FIM DA ALTERAÇÃO NA QUERY +++++

        params = [data_inicio, data_fim, data_inicio, data_fim, data_inicio]
        cursor_local.execute(query, params)
        
        status_eventos = []
        for row in cursor_local.fetchall():
            start_time = max(row.DataHoraInicio, data_inicio)
            end_time = min(row.DataHoraFim, data_fim)

            # +++++ ALTERAÇÃO AQUI: Adicionando o Código da Ordem aos dados +++++
            status_eventos.append([
                row.NomeMaquina,
                row.MotivoOuStatus,
                start_time.isoformat(),
                end_time.isoformat(),
                row.CodigoOrdem  # << NOVO DADO ENVIADO PARA O HTML
            ])

        return render_template(
            'gantt_status_maquinas.html', 
            timeline_data_json=json.dumps(status_eventos),
            data_filtro=data_filtro_str
        )

    except Exception as e:
        logger.error(f"Erro em /gantt_status_maquinas: {e}", exc_info=True)
        flash("Ocorreu um erro ao gerar o gráfico de status.", "error")
        return redirect(url_for('relatorios'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            

# Em planner_app.py, SUBSTITUA a função da linha 7088:

@app.route('/relatorio_ciclos', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/relatorio_ciclos')
def relatorio_ciclos():
    conn_local = None
    resultados_tabela = []
    chart_data = {'labels': [], 'datasets': []}
    recursos = []
    turnos = [] # <<< ADICIONADO
    kpis_ciclos = {
        'total_ciclos': 0, 'media_real_s': 0.0, 'media_planejada_s': 0.0,
    }

    data_inicio_padrao = (datetime.now() - timedelta(days=1)).strftime('%Y-%m-%d')
    data_fim_padrao = datetime.now().strftime('%Y-%m-%d')

    # +++++ INÍCIO DA ALTERAÇÃO 1 (Adiciona id_turno) +++++
    filtros = {
        "data_inicio": request.form.get("data_inicio") if request.method == 'POST' else request.args.get("data_inicio", data_inicio_padrao),
        "data_fim": request.form.get("data_fim") if request.method == 'POST' else request.args.get("data_fim", data_fim_padrao),
        "id_recurso": request.form.get("id_recurso") if request.method == 'POST' else request.args.get("id_recurso", ""),
        "id_turno": request.form.get("id_turno") if request.method == 'POST' else request.args.get("id_turno", ""), # <<< ADICIONADO
        "codigo_ordem": request.form.get("codigo_ordem") if request.method == 'POST' else request.args.get("codigo_ordem", ""),
        "numero_operacao": request.form.get("numero_operacao") if request.method == 'POST' else request.args.get("numero_operacao", "")
    }
    # +++++ FIM DA ALTERAÇÃO 1 +++++

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina")
        recursos = cursor_local.fetchall()
        cursor_local.execute("SELECT IDTurno, NomeTurno FROM TBL_Turno WHERE Ativo = 1 ORDER BY NomeTurno") # <<< ADICIONADO
        turnos = cursor_local.fetchall() # <<< ADICIONADO

        # +++++ INÍCIO DA ALTERAÇÃO 2 (Condição do IF) +++++
        if request.method == 'POST' or any(f for f in [filtros['id_recurso'], filtros['id_turno'], filtros['codigo_ordem'], filtros['numero_operacao']] if f):
        # +++++ FIM DA ALTERAÇÃO 2 +++++
            
            logger.info(f"Gerando relatório de ciclos (últimos 25) com filtros: {filtros}")

            try:
                data_inicio_dt = datetime.strptime(filtros["data_inicio"], '%Y-%m-%d')
                data_fim_dt = datetime.strptime(filtros["data_fim"], '%Y-%m-%d')
            except ValueError:
                flash("Formato de data inválido.", "error")
                return render_template('relatorio_ciclos.html',
                                       recursos=recursos, filtros=filtros,
                                       turnos=turnos, # <<< ADICIONADO
                                       resultados_tabela=resultados_tabela,
                                       kpis=kpis_ciclos, 
                                       chart_data_json=json.dumps(chart_data, cls=DecimalEncoder))

            base_cte = """
                WITH EventosComDataTurno AS (
                    SELECT 
                        E.IDEvento, E.DataHoraEvento, E.IDExecucao, E.IDMaquina, 
                        E.IDOrdemProducao, E.IDOrdemOperacao, E.IDTurno,
                        T.NomeTurno, -- <<< ADICIONADO
                        T.IniciaDiaAnterior, T.HoraInicio AS HoraInicioTurno,
                        CASE
                            WHEN T.IniciaDiaAnterior = 1 AND CAST(E.DataHoraEvento AS TIME) < CAST(T.HoraInicio AS TIME)
                            THEN CAST(DATEADD(day, -1, E.DataHoraEvento) AS DATE)
                            ELSE CAST(E.DataHoraEvento AS DATE)
                        END AS DataReferenciaTurno
                    FROM VW_EventoProducaoComCicloReal E WITH (NOLOCK)
                    LEFT JOIN TBL_Turno T ON E.IDTurno = T.IDTurno
                    WHERE E.TipoValor = 'BOA'
                )
            """

            sql = base_cte + """
                , EventosComLag AS (
                    SELECT 
                        EVT.*, -- <<< Traz todas as colunas do CTE, incluindo NomeTurno
                        LAG(EVT.DataHoraEvento, 1) OVER (PARTITION BY EVT.IDMaquina, EVT.IDOrdemOperacao ORDER BY EVT.DataHoraEvento) as HoraEventoAnterior
                    FROM EventosComDataTurno EVT
                    WHERE EVT.DataReferenciaTurno BETWEEN ? AND ?
            """
            params = [data_inicio_dt, data_fim_dt]

            if filtros["id_recurso"]:
                sql += " AND EVT.IDMaquina = ?"
                params.append(int(filtros["id_recurso"]))
                
            # +++++ INÍCIO DA ALTERAÇÃO 3 (Filtro de Turno) +++++
            if filtros["id_turno"]:
                sql += " AND EVT.IDTurno = ?"
                params.append(int(filtros["id_turno"]))
            # +++++ FIM DA ALTERAÇÃO 3 +++++
            
            sql += """
                ), CiclosCalculados AS (
                    SELECT EL.*,
                           CAST(DATEDIFF(MILLISECOND, EL.HoraEventoAnterior, EL.DataHoraEvento) AS FLOAT) / 1000.0 as CicloRealSegundos
                    FROM EventosComLag EL
                    WHERE EL.HoraEventoAnterior IS NOT NULL AND EL.DataHoraEvento > EL.HoraEventoAnterior AND DATEDIFF(MILLISECOND, EL.HoraEventoAnterior, EL.DataHoraEvento) > 100
                ),
                Ultimos25CiclosFiltrados AS (
                    SELECT TOP 25
                        C.DataHoraEvento, R.NomeMaquina, O.CodigoOrdem, OPO.NumeroOperacao, OPO.Descricao AS DescricaoOperacao,
                        P.CodigoProduto, P.NomeProduto, C.CicloRealSegundos, C.IDOrdemProducao, C.IDOrdemOperacao, C.IDMaquina,
                        ISNULL(C.NomeTurno, 'N/A') AS NomeTurno, -- <<< ADICIONADO
                        CASE WHEN O.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.TempoCicloPadraoSegundos
                             ELSE P.TempoCicloSegundos END AS CicloPlanejadoSegundos
                    FROM CiclosCalculados C
                    JOIN TBL_OrdemProducao O WITH (NOLOCK) ON C.IDOrdemProducao = O.IDOrdem
                    JOIN TBL_Produto P WITH (NOLOCK) ON O.IDProduto = P.IDProduto
                    JOIN TBL_Recurso R WITH (NOLOCK) ON C.IDMaquina = R.IDMaquina
                    LEFT JOIN TBL_OrdemProducao_Operacoes OPO WITH (NOLOCK) ON C.IDOrdemOperacao = OPO.IDOrdemOperacao
                    LEFT JOIN TBL_RecursoProduto RP WITH (NOLOCK) ON C.IDMaquina = RP.IDRecurso AND O.IDProduto = RP.IDProduto
                    WHERE 1=1
            """

            if filtros["codigo_ordem"]:
                 sql += " AND O.CodigoOrdem LIKE ?"
                 params.append(f"%{filtros['codigo_ordem']}%")
            if filtros["numero_operacao"]:
                 sql += " AND OPO.NumeroOperacao = ?"
                 params.append(filtros['numero_operacao'])

            sql += """
                    ORDER BY C.DataHoraEvento DESC
                )
                SELECT *
                FROM Ultimos25CiclosFiltrados
                ORDER BY DataHoraEvento ASC;
            """
            
            logger.debug(f"Executando query de ciclos (últimos 25, com DataRef) com {len(params)} params: {params}")
            cursor_local.execute(sql, params)
            resultados_raw = cursor_local.fetchall()
            logger.info(f"Consulta de ciclos (últimos 25, com DataRef) retornou {len(resultados_raw)} registros.")
            
            labels_chart = []
            data_real = []
            data_planned = []
            lista_ciclos_reais = [] 
            lista_ciclos_planejados = [] 

            if resultados_raw:
                kpis_ciclos['total_ciclos'] = len(resultados_raw) 
                for row in resultados_raw:
                    try:
                        row_dict = dict(zip([column[0] for column in cursor_local.description], row))
                    except Exception as e:
                        logger.error(f"Erro ao converter linha DB->dict: {e} - Linha: {row}")
                        continue
                        
                    # +++++ INÍCIO DA ALTERAÇÃO 4 (Adiciona NomeTurno ao dict) +++++
                    row_dict['CicloRealFmt'] = f"{row_dict.get('CicloRealSegundos', 0):.2f}".replace('.', ',') if row_dict.get('CicloRealSegundos') is not None else "N/A"
                    row_dict['CicloPlanejadoFmt'] = f"{row_dict.get('CicloPlanejadoSegundos', 0):.2f}".replace('.', ',') if row_dict.get('CicloPlanejadoSegundos') is not None else "N/A"
                    row_dict['DataHoraEventoFmt'] = row_dict['DataHoraEvento'].strftime('%d/%m %H:%M:%S.%f')[:-3] if row_dict.get('DataHoraEvento') else "N/A"
                    row_dict['OperacaoFmt'] = f"{row_dict.get('NumeroOperacao','')} - {row_dict.get('DescricaoOperacao', 'N/A')}" if row_dict.get('NumeroOperacao') else 'N/A'
                    row_dict['ProdutoFmt'] = f"{row_dict.get('CodigoProduto','')} - {row_dict.get('NomeProduto', 'N/A')}" if row_dict.get('CodigoProduto') else 'N/A'
                    # row_dict['NomeTurno'] já está vindo da query (SELECT *)
                    resultados_tabela.append(row_dict)
                    # +++++ FIM DA ALTERAÇÃO 4 +++++

                    labels_chart.append(row_dict.get('DataHoraEventoFmt', ''))
                    ciclo_real_val = row_dict.get('CicloRealSegundos')
                    ciclo_plan_val = row_dict.get('CicloPlanejadoSegundos')
                    data_real.append(ciclo_real_val if ciclo_real_val is not None else 0)
                    data_planned.append(ciclo_plan_val if ciclo_plan_val is not None else 0)
                    if ciclo_real_val is not None:
                        lista_ciclos_reais.append(ciclo_real_val)
                    if ciclo_plan_val is not None:
                        lista_ciclos_planejados.append(ciclo_plan_val)

                if lista_ciclos_reais:
                    kpis_ciclos['media_real_s'] = np.mean(lista_ciclos_reais)
                if lista_ciclos_planejados:
                    kpis_ciclos['media_planejada_s'] = np.mean(lista_ciclos_planejados)
                chart_data = {
                    'labels': labels_chart,
                    'datasets': [
                        {'label': 'Ciclo Real (s)', 'data': data_real, 'backgroundColor': 'rgba(255, 99, 132, 0.6)', 'borderColor': 'rgb(255, 99, 132)', 'borderWidth': 1, 'order': 2 },
                        {'label': 'Ciclo Planejado (s)', 'data': data_planned, 'type': 'line', 'borderColor': 'rgb(75, 192, 192)', 'backgroundColor': 'rgba(75, 192, 192, 0.5)', 'tension': 0.1, 'fill': False, 'pointRadius': 0, 'borderDash': [5, 5], 'order': 1 }
                    ]
                }
            else:
                 flash("Nenhum ciclo encontrado para os filtros selecionados.", "info")
        
        chart_data_json_str = json.dumps(chart_data, cls=DecimalEncoder)
        logger.debug(f"Chart JSON (últimos 25, com DataRef) sendo enviado: {chart_data_json_str[:200]}...")

        return render_template('relatorio_ciclos.html',
                               recursos=recursos,
                               turnos=turnos, # <<< ADICIONADO
                               filtros=filtros,
                               resultados_tabela=resultados_tabela,
                               kpis=kpis_ciclos,
                               chart_data_json=chart_data_json_str)

    except pyodbc.Error as db_err:
        logger.error(f"Erro de banco de dados em relatorio_ciclos: {db_err}", exc_info=True)
        flash(f"Erro de banco de dados ao gerar o relatório: {db_err}", "danger")
        return render_template('relatorio_ciclos.html',
                               recursos=recursos, filtros=filtros,
                               turnos=turnos, # <<< ADICIONADO
                               resultados_tabela=[], kpis=kpis_ciclos, chart_data_json='{}')
    except Exception as e:
        logger.error(f"Erro inesperado em relatorio_ciclos: {e}", exc_info=True)
        flash("Ocorreu um erro inesperado ao gerar o relatório de ciclos.", "danger")
        return redirect(url_for('relatorios'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

#planner_app.py

@app.route('/estudo_ciclos', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/estudo_ciclos') # Lembre-se de cadastrar esta permissão
def estudo_ciclos():
    conn_local = None
    produtos = []
    maquinas = []
    data_fim_padrao = datetime.now().strftime('%Y-%m-%d')
    data_inicio_padrao = (datetime.now() - timedelta(days=7)).strftime('%Y-%m-%d')

    # Define a estrutura de filtros NO INÍCIO para GET e POST
    filtros = {
        'data_inicio': request.form.get('data_inicio', data_inicio_padrao) if request.method == 'POST' else data_inicio_padrao,
        'data_fim': request.form.get('data_fim', data_fim_padrao) if request.method == 'POST' else data_fim_padrao,
        'id_produto': request.form.get('id_produto') if request.method == 'POST' else None,
        'id_maquina': request.form.get('id_maquina') if request.method == 'POST' else None,
        'codigo_ordem': request.form.get('codigo_ordem', '') if request.method == 'POST' else ''
    }
    # Inicializa variáveis para o template
    dados_grafico_json = '{}'
    ciclo_padrao_info = {'valor_segundos': None, 'origem': 'Não determinado'}
    kpis = {
        'total_ciclos': 0, 'cont_lentos': 0, 'perc_lentos': 0.0,
        'cont_padrao': 0, 'perc_padrao': 0.0, 'cont_rapidos': 0, 'perc_rapidos': 0.0
    }
    resultados_tabela = [] # Inicializa a tabela vazia

    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # Sempre busca os dados para os dropdowns de filtro
        cursor_local.execute("SELECT IDProduto, CodigoProduto, NomeProduto FROM TBL_Produto WHERE Habilitado = 1 ORDER BY NomeProduto")
        produtos = cursor_local.fetchall()
        cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1 ORDER BY NomeMaquina")
        maquinas = cursor_local.fetchall()

        # Executa a lógica principal apenas se for um POST (submissão de formulário)
        if request.method == 'POST':
            # --- Bloco de Validação Centralizado ---
            if not filtros['id_maquina']:
                flash("Por favor, selecione uma máquina.", "warning")
                # Se a validação falhar, renderiza a página com a mensagem de erro
                return render_template('estudo_ciclos.html', produtos=produtos, maquinas=maquinas, filtros=filtros, dados_grafico_json=dados_grafico_json, ciclo_padrao_info=ciclo_padrao_info, kpis=kpis, resultados_tabela=resultados_tabela) # Adicionado resultados_tabela

            id_produto_int = int(filtros['id_produto']) if filtros['id_produto'] else None
            id_ordem_encontrada = None
            if filtros['codigo_ordem']:
                cursor_local.execute("SELECT IDOrdem, IDProduto FROM TBL_OrdemProducao WHERE CodigoOrdem = ?", filtros['codigo_ordem'])
                ordem_row = cursor_local.fetchone()
                if ordem_row:
                    id_ordem_encontrada = ordem_row.IDOrdem
                    if not id_produto_int: id_produto_int = ordem_row.IDProduto
                else:
                    flash(f"Ordem com código '{filtros['codigo_ordem']}' não encontrada.", "warning")

            # Validação final para garantir que temos um produto para analisar
            if not id_produto_int:
                flash("É necessário selecionar um produto ou informar uma ordem válida.", "warning")
                # Renderiza a página com a mensagem de erro
                return render_template('estudo_ciclos.html', produtos=produtos, maquinas=maquinas, filtros=filtros, dados_grafico_json=dados_grafico_json, ciclo_padrao_info=ciclo_padrao_info, kpis=kpis, resultados_tabela=resultados_tabela) # Adicionado resultados_tabela
            # --- Fim do Bloco de Validação ---


            # --- Início do Processamento (se a validação passou) ---
            id_maquina_int = int(filtros['id_maquina'])
            ciclo_padrao_segundos = 0.0

            try:
                usar_tempo_recurso = False
                if id_ordem_encontrada:
                    cursor_local.execute("SELECT UsarTempoCicloRecurso FROM TBL_OrdemProducao WHERE IDOrdem = ?", id_ordem_encontrada)
                    ordem_config_row = cursor_local.fetchone()
                    if ordem_config_row and ordem_config_row.UsarTempoCicloRecurso == 1: usar_tempo_recurso = True

                if usar_tempo_recurso:
                    cursor_local.execute("SELECT TempoCicloPadraoSegundos FROM TBL_RecursoProduto WHERE IDRecurso = ? AND IDProduto = ?", (id_maquina_int, id_produto_int))
                    recurso_produto_row = cursor_local.fetchone()
                    if recurso_produto_row and recurso_produto_row.TempoCicloPadraoSegundos is not None:
                        ciclo_padrao_segundos = float(recurso_produto_row.TempoCicloPadraoSegundos)
                        ciclo_padrao_info['origem'] = 'Config. Recurso x Produto'
                    else: # Fallback
                        logger.warning(f"OP {filtros['codigo_ordem']} pede tempo específico, mas não há cadastro. Usando tempo base do produto ID {id_produto_int}.")
                        cursor_local.execute("SELECT TempoCicloSegundos FROM TBL_Produto WHERE IDProduto = ?", id_produto_int)
                        produto_row = cursor_local.fetchone()
                        if produto_row and produto_row.TempoCicloSegundos is not None:
                            ciclo_padrao_segundos = float(produto_row.TempoCicloSegundos)
                            ciclo_padrao_info['origem'] = 'Cadastro do Produto (Fallback)'
                        else: raise ValueError("Ciclo padrão não encontrado (Fallback falhou)")
                else: # Usa tempo do produto
                    cursor_local.execute("SELECT TempoCicloSegundos FROM TBL_Produto WHERE IDProduto = ?", id_produto_int)
                    produto_row = cursor_local.fetchone()
                    if produto_row and produto_row.TempoCicloSegundos is not None:
                        ciclo_padrao_segundos = float(produto_row.TempoCicloSegundos)
                        ciclo_padrao_info['origem'] = 'Cadastro do Produto'
                    else: raise ValueError("Ciclo padrão não encontrado no produto")

                if ciclo_padrao_segundos <= 0: raise ValueError("O ciclo padrão configurado é inválido (0 ou menor).")
                ciclo_padrao_info['valor_segundos'] = round(ciclo_padrao_segundos, 3)

            except ValueError as ve:
                flash(str(ve), "error")
                return render_template('estudo_ciclos.html', produtos=produtos, maquinas=maquinas, filtros=filtros, dados_grafico_json=dados_grafico_json, ciclo_padrao_info=ciclo_padrao_info, kpis=kpis, resultados_tabela=resultados_tabela) # Adicionado resultados_tabela

            # Lógica para buscar os ciclos reais
            data_inicio_dt = datetime.strptime(filtros['data_inicio'], '%Y-%m-%d')
            data_fim_dt = datetime.strptime(filtros['data_fim'], '%Y-%m-%d').replace(hour=23, minute=59, second=59)

            sql_ciclos_final = """
                WITH EventosOrdenados AS (
                    SELECT E.DataHoraEvento, LAG(E.DataHoraEvento, 1) OVER (ORDER BY E.DataHoraEvento) as HoraEventoAnterior
                    FROM VW_EventoProducaoComCicloReal E
                    JOIN TBL_ExecucaoOP EX ON E.IDExecucao = EX.IDExecucao
                    JOIN TBL_OrdemProducao OP ON EX.IDOrdem = OP.IDOrdem
                    WHERE E.IDMaquina = ? AND E.TipoValor = 'BOA' AND E.DataHoraEvento BETWEEN ? AND ? AND OP.IDProduto = ? {filtro_ordem}
                ), CiclosCalculados AS (
                    SELECT CAST(DATEDIFF(MILLISECOND, HoraEventoAnterior, DataHoraEvento) AS FLOAT) / 1000.0 as CicloRealSegundos
                    FROM EventosOrdenados WHERE HoraEventoAnterior IS NOT NULL
                ) SELECT CicloRealSegundos FROM CiclosCalculados WHERE CicloRealSegundos > 0.1;
            """.format(filtro_ordem=" AND OP.IDOrdem = ? " if id_ordem_encontrada else "")
            params_ciclos = [id_maquina_int, data_inicio_dt, data_fim_dt, id_produto_int]
            if id_ordem_encontrada: params_ciclos.append(id_ordem_encontrada)

            cursor_local.execute(sql_ciclos_final, params_ciclos)
            ciclos_reais = cursor_local.fetchall()

            if ciclos_reais:
                limite_superior = ciclo_padrao_segundos * 1.10
                limite_inferior = ciclo_padrao_segundos * 0.90

                for ciclo_row in ciclos_reais:
                    ciclo_atual = ciclo_row.CicloRealSegundos
                    if ciclo_atual >= limite_superior: kpis['cont_lentos'] += 1
                    elif ciclo_atual <= limite_inferior: kpis['cont_rapidos'] += 1
                    else: kpis['cont_padrao'] += 1

                total_ciclos_calc = len(ciclos_reais)
                kpis['total_ciclos'] = total_ciclos_calc

                if total_ciclos_calc > 0:
                    kpis['perc_lentos'] = (kpis['cont_lentos'] * 100.0 / total_ciclos_calc)
                    kpis['perc_padrao'] = (kpis['cont_padrao'] * 100.0 / total_ciclos_calc)
                    kpis['perc_rapidos'] = (kpis['cont_rapidos'] * 100.0 / total_ciclos_calc)

                    chart_data = {
                        'labels': [f'Ciclos Lentos (>= {limite_superior:.2f}s)', f'Ciclos Padrão (> {limite_inferior:.2f}s e < {limite_superior:.2f}s)', f'Ciclos Rápidos (<= {limite_inferior:.2f}s)'],
                        'data': [kpis['cont_lentos'], kpis['cont_padrao'], kpis['cont_rapidos']]
                    }
                    dados_grafico_json = json.dumps(chart_data)
            else:
                flash("Nenhum ciclo válido foi encontrado para os filtros selecionados.", "info")
            # --- Fim do Processamento ---

        # ========= INÍCIO DA CORREÇÃO =========
        # Este return será executado tanto para GET quanto para POST (se não houver redirect ou erro)
        return render_template('estudo_ciclos.html',
                               produtos=produtos,
                               maquinas=maquinas,
                               filtros=filtros,
                               dados_grafico_json=dados_grafico_json,
                               ciclo_padrao_info=ciclo_padrao_info,
                               kpis=kpis,
                               resultados_tabela=resultados_tabela) # Adicionado resultados_tabela
        # ========= FIM DA CORREÇÃO =========

    except Exception as e:
        logger.error(f"Erro inesperado na rota /estudo_ciclos: {e}", exc_info=True)
        # Verifica se já existe uma mensagem de erro/aviso antes de adicionar uma genérica
        if not get_flashed_messages(category_filter=["error", "warning"]):
             flash("Ocorreu um erro inesperado ao gerar o estudo.", "error")
        # Se ocorrer um erro grave, redireciona para a página de relatórios
        return redirect(url_for('relatorios'))
    finally:
        if conn_local:
            devolver_conexao(conn_local)

    
# Em planner_app.py, SUBSTITUA a função da linha 7616:

@app.route('/relatorio_ciclos/exportar', methods=['POST'])
@login_requerido
@permissao_requerida('/relatorio_ciclos') 
def exportar_relatorio_ciclos():
    conn_local = None
    try:
        data = request.json 
        export_type = data.get('exportType', 'ambos')
        # +++++ INÍCIO DA ALTERAÇÃO 1 (Recebe id_turno) +++++
        filtros = {
            "data_inicio": data.get("data_inicio"),
            "data_fim": data.get("data_fim"),
            "id_recurso": data.get("id_recurso"),
            "id_turno": data.get("id_turno"), # <<< ADICIONADO
            "codigo_ordem": data.get("codigo_ordem"),
            "numero_operacao": data.get("numero_operacao") 
        }
        # +++++ FIM DA ALTERAÇÃO 1 +++++

        logger.info(f"Iniciando exportação do relatório de ciclos com filtros: {filtros} (Tipo: {export_type})")

        try:
            data_inicio_dt = datetime.strptime(filtros["data_inicio"], '%Y-%m-%d')
            data_fim_dt = datetime.strptime(filtros["data_fim"], '%Y-%m-%d')
        except (ValueError, TypeError):
             logger.error("Datas inválidas recebidas para exportação.")
             return jsonify({"error": "Datas de filtro inválidas."}), 400

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor() 

        # +++++ INÍCIO DA ALTERAÇÃO 2 (Query de Exportação) +++++
        base_cte = """
            WITH EventosComDataTurno AS (
                SELECT 
                    E.IDEvento, E.DataHoraEvento, E.IDExecucao, E.IDMaquina, 
                    E.IDOrdemProducao, E.IDOrdemOperacao, E.IDTurno,
                    T.NomeTurno, -- <<< ADICIONADO
                    T.IniciaDiaAnterior, T.HoraInicio AS HoraInicioTurno,
                    CASE
                        WHEN T.IniciaDiaAnterior = 1 AND CAST(E.DataHoraEvento AS TIME) < CAST(T.HoraInicio AS TIME)
                        THEN CAST(DATEADD(day, -1, E.DataHoraEvento) AS DATE)
                        ELSE CAST(E.DataHoraEvento AS DATE)
                    END AS DataReferenciaTurno
                FROM VW_EventoProducaoComCicloReal E WITH (NOLOCK)
                LEFT JOIN TBL_Turno T ON E.IDTurno = T.IDTurno
                WHERE E.TipoValor = 'BOA'
            )
        """
        
        sql_export = base_cte + """
            , EventosComLag AS (
                SELECT 
                    EVT.*, -- <<< Traz todas as colunas, incluindo NomeTurno
                    LAG(EVT.DataHoraEvento, 1) OVER (PARTITION BY EVT.IDMaquina, EVT.IDOrdemOperacao ORDER BY EVT.DataHoraEvento) as HoraEventoAnterior
                FROM EventosComDataTurno EVT
                WHERE EVT.DataReferenciaTurno BETWEEN ? AND ?
        """
        params_export = [data_inicio_dt, data_fim_dt]

        if filtros["id_recurso"]:
            sql_export += " AND EVT.IDMaquina = ?"
            params_export.append(int(filtros["id_recurso"]))
        
        if filtros["id_turno"]: # <<< ADICIONADO
            sql_export += " AND EVT.IDTurno = ?"
            params_export.append(int(filtros["id_turno"]))

        sql_export += """
            ), CiclosCalculados AS (
                SELECT EL.*,
                       CAST(DATEDIFF(MILLISECOND, EL.HoraEventoAnterior, EL.DataHoraEvento) AS FLOAT) / 1000.0 as CicloRealSegundos
                FROM EventosComLag EL
                WHERE EL.HoraEventoAnterior IS NOT NULL AND EL.DataHoraEvento > EL.HoraEventoAnterior AND DATEDIFF(MILLISECOND, EL.HoraEventoAnterior, EL.DataHoraEvento) > 100
            ),
            TodosCiclosFiltrados AS (
                SELECT 
                    C.DataHoraEvento, R.NomeMaquina, O.CodigoOrdem,
                    OPO.NumeroOperacao, OPO.Descricao AS DescricaoOperacao, 
                    P.CodigoProduto, P.NomeProduto, C.CicloRealSegundos,
                    ISNULL(C.NomeTurno, 'N/A') AS NomeTurno, -- <<< ADICIONADO
                    CASE WHEN O.UsarTempoCicloRecurso = 1 AND RP.IDRecursoProduto IS NOT NULL THEN RP.TempoCicloPadraoSegundos
                         ELSE P.TempoCicloSegundos END AS CicloPlanejadoSegundos
                FROM CiclosCalculados C
                JOIN TBL_OrdemProducao O WITH (NOLOCK) ON C.IDOrdemProducao = O.IDOrdem
                JOIN TBL_Produto P WITH (NOLOCK) ON O.IDProduto = P.IDProduto
                JOIN TBL_Recurso R WITH (NOLOCK) ON C.IDMaquina = R.IDMaquina
                LEFT JOIN TBL_OrdemProducao_Operacoes OPO WITH (NOLOCK) ON C.IDOrdemOperacao = OPO.IDOrdemOperacao 
                LEFT JOIN TBL_RecursoProduto RP WITH (NOLOCK) ON C.IDMaquina = RP.IDRecurso AND O.IDProduto = RP.IDProduto
                WHERE 1=1
        """
        # +++++ FIM DA ALTERAÇÃO 2 +++++
        
        if filtros["codigo_ordem"]:
             sql_export += " AND O.CodigoOrdem LIKE ?"
             params_export.append(f"%{filtros['codigo_ordem']}%")
        if filtros["numero_operacao"]: 
             sql_export += " AND OPO.NumeroOperacao = ?"
             params_export.append(filtros['numero_operacao'])

        sql_export += """
            )
            SELECT *
            FROM TodosCiclosFiltrados
            ORDER BY DataHoraEvento ASC;
        """
        
        df = pd.DataFrame() 
        if export_type in ['tabela', 'ambos']:
            logger.debug("Executando query para dados da tabela de exportação...")
            df = pd.read_sql(sql_export, conn_local, params=params_export)
            logger.info(f"Consulta para exportação retornou {len(df)} ciclos.")

            if not df.empty:
                df['Ciclo Real (s)'] = df['CicloRealSegundos'].apply(lambda x: f"{x:.2f}".replace('.', ',') if pd.notna(x) else '')
                df['Ciclo Planejado (s)'] = df['CicloPlanejadoSegundos'].apply(lambda x: f"{x:.2f}".replace('.', ',') if pd.notna(x) else '')
                df['Data/Hora'] = pd.to_datetime(df['DataHoraEvento']).dt.strftime('%d/%m/%Y %H:%M:%S')
                df['Produto'] = df['CodigoProduto'] + ' - ' + df['NomeProduto']
                df['Operação'] = df['NumeroOperacao'].astype(str) + ' - ' + df['DescricaoOperacao'] 
                
                # +++++ INÍCIO DA ALTERAÇÃO 3 (Formatação do Excel) +++++
                df.rename(columns={'NomeMaquina': 'Recurso', 'CodigoOrdem': 'Ordem', 'NomeTurno': 'Turno'}, inplace=True)
                df = df[['Data/Hora', 'Recurso', 'Turno', 'Ordem', 'Operação', 'Produto', 'Ciclo Real (s)', 'Ciclo Planejado (s)']]
                # +++++ FIM DA ALTERAÇÃO 3 +++++
            else:
                 logger.warning("Nenhum dado encontrado para a tabela de exportação com os filtros aplicados.")
        
        output = io.BytesIO()
        with pd.ExcelWriter(output, engine='openpyxl') as writer:
            df.to_excel(writer, index=False, sheet_name='Ciclos')
            worksheet = writer.sheets['Ciclos'] 

            if export_type in ['grafico', 'ambos'] and 'chartImage' in data and data['chartImage']:
                try:
                    logger.info("Adicionando gráfico ao arquivo Excel...")
                    base64_image_data = data['chartImage'].split(',')[1]
                    image_data = base64.b64decode(base64_image_data)
                    img = Image(io.BytesIO(image_data))
                    img.anchor = 'A' + str(len(df) + 3)
                    worksheet.add_image(img)
                    logger.info("Gráfico adicionado com sucesso.")
                except Exception as img_err:
                     logger.error(f"Erro ao adicionar imagem do gráfico ao Excel: {img_err}", exc_info=True)

        output.seek(0) 

        logger.info("Arquivo Excel gerado. Enviando para download...")
        return send_file(
            output,
            as_attachment=True,
            download_name='relatorio_de_ciclos.xlsx',
            mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet'
        )

    except Exception as e:
        logger.error(f"Erro CRÍTICO ao exportar relatório de ciclos: {e}", exc_info=True)
        return jsonify({"error": f"Falha ao gerar o arquivo Excel: {str(e)}"}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
@app.route('/manual/registrar_producao', methods=['POST'])
@login_requerido
# @permissao_requerida('/apontamento_manual') # Descomente e crie a permissão se desejar controle mais fino
def manual_registrar_producao():
    """
    Recebe dados de apontamento manual (peças boas ou refugo) via JSON POST,
    valida, garante que a máquina esteja em status 'Produzindo',
    e registra o evento no banco de dados com OrigemEvento='MANUAL'.
    """
    conn_local = None
    id_maquina = None # Definido fora para uso no log de erro
    try:
        data = request.get_json()
        if not data:
            logger.warning("Recebida requisição sem corpo JSON em /manual/registrar_producao")
            return jsonify({'success': False, 'message': 'Dados da requisição inválidos (JSON esperado).'}), 400

        id_maquina = data.get('id_maquina', type=int)
        quantidade_str = data.get('quantidade')
        tipo_valor = data.get('tipo_valor') # Deverá ser 'BOA' ou 'REFUGO'
        id_motivo_refugo = data.get('id_motivo_refugo', type=int) if tipo_valor == 'REFUGO' else None
        observacao = data.get('observacao', '') # Captura a observação (opcional)

        # --- Validação robusta dos inputs ---
        if not id_maquina:
            logger.warning("Apontamento manual recebido sem ID da máquina.")
            return jsonify({'success': False, 'message': 'ID da máquina não fornecido.'}), 400
        if not quantidade_str:
            logger.warning(f"Apontamento manual para maq {id_maquina} sem quantidade.")
            return jsonify({'success': False, 'message': 'Quantidade não fornecida.'}), 400
        if tipo_valor not in ['BOA', 'REFUGO']:
            logger.warning(f"Apontamento manual para maq {id_maquina} com tipo inválido: {tipo_valor}")
            return jsonify({'success': False, 'message': "Tipo de valor inválido (deve ser 'BOA' ou 'REFUGO')."}), 400
        if tipo_valor == 'REFUGO' and not id_motivo_refugo:
            logger.warning(f"Apontamento manual de REFUGO para maq {id_maquina} sem motivo.")
            return jsonify({'success': False, 'message': 'Motivo do refugo é obrigatório para registrar refugo.'}), 400

        try:
            quantidade = float(str(quantidade_str).replace(',', '.'))
            if quantidade <= 0:
                raise ValueError("Quantidade deve ser positiva.")
        except (ValueError, TypeError):
            logger.warning(f"Apontamento manual para maq {id_maquina} com quantidade inválida: {quantidade_str}")
            return jsonify({'success': False, 'message': 'Quantidade inválida. Use números positivos (ex: 10 ou 10,5).'}), 400
        # --- Fim da Validação ---

        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        # 1. Verifica se a máquina existe e é MANUAL (automatico == 0)
        cursor_local.execute("SELECT automatico FROM TBL_Recurso WHERE IDMaquina = ?", id_maquina)
        recurso_info = cursor_local.fetchone()
        if not recurso_info:
            logger.error(f"Tentativa de apontamento manual para máquina inexistente: ID {id_maquina}")
            return jsonify({'success': False, 'message': f'Máquina ID {id_maquina} não encontrada.'}), 404
        # Acessa a coluna correta (automatico)
        if recurso_info.automatico == 1:
            logger.warning(f"Tentativa de apontamento manual para máquina sensorizada (automática): ID {id_maquina}")
            return jsonify({'success': False, 'message': f'Máquina ID {id_maquina} tem apontamento automático. Apontamento manual não permitido.'}), 403

        # 2. Encontra a execução ativa (OP em Execução) - Essencial para vincular o apontamento
        cursor_local.execute("""
            SELECT TOP 1
                E.IDExecucao, E.IDOrdem, E.IDOperador AS IDOperadorExecucao, R.IDTipo AS IDTipoRecurso,
                E.IDOrdemOperacao
            FROM TBL_ExecucaoOP E
            JOIN TBL_Recurso R ON E.IDMaquina = R.IDMaquina
            WHERE E.IDMaquina = ? AND E.Status = 'Em Execucao'
            ORDER BY E.DataHoraInicio DESC
        """, id_maquina)
        execucao_info = cursor_local.fetchone()

        if not execucao_info:
            logger.warning(f"Tentativa de apontamento manual para máquina {id_maquina} sem OP ativa.")
            return jsonify({'success': False, 'message': 'Nenhuma Ordem de Produção ativa encontrada para esta máquina. Inicie uma OP antes de apontar.'}), 400

        # 3. GARANTE que o status da máquina seja "Produzindo" (Status=1)
        logger.debug(f"Garantindo status 'Produzindo' para máquina manual {id_maquina} antes do apontamento.")
        _update_machine_status(conn_local, cursor_local, id_maquina, 1, obs_evento="Produção manual registrada")

        # 4. Identifica o turno atual da máquina
        id_turno_maquina = identificar_turno_da_maquina(conn_local, cursor_local, id_maquina)
        data_hora_evento = datetime.now() # Usar o momento exato do apontamento no servidor

        # 5. Insere o evento de produção/refugo na VW (que deve direcionar para TBL_EventoProducao)
        colunas_insert = """
            IDExecucao, IDOrdemProducao, IDMaquina, IDOperador, IDTurno, IDTipoRecurso,
            Quantidade, TipoValor, OrigemEvento, ObsEvento, DataHoraEvento, IDTipoEvento,
            IDOrdemOperacao
        """
        valores_placeholders = "?, ?, ?, ?, ?, ?, ?, ?, 'MANUAL', ?, ?, ?, ?" # OrigemEvento fixo como MANUAL

        # Usa o ID do usuário LOGADO como o operador que realizou o apontamento
        id_operador_apontamento = session.get('usuario_id')
        if not id_operador_apontamento:
             # Fallback ou erro se não houver usuário logado (deve ter por causa do @login_requerido)
             logger.error(f"Não foi possível obter o ID do usuário logado para o apontamento manual na máquina {id_maquina}")
             return jsonify({'success': False, 'message': 'Erro interno: Usuário não identificado.'}), 500


        params_insert = [
            execucao_info.IDExecucao,
            execucao_info.IDOrdem,
            id_maquina,
            id_operador_apontamento, # ID do usuário que fez a ação no sistema
            id_turno_maquina,
            execucao_info.IDTipoRecurso,
            quantidade,
            tipo_valor,
            observacao, # Observação vinda do formulário/modal
            data_hora_evento,
            1 if tipo_valor == 'BOA' else 2, # IDTipoEvento (1=Produção, 2=Ajuste/Refugo)
            execucao_info.IDOrdemOperacao # ID da Operação vinculada à Execução
        ]

        if tipo_valor == 'REFUGO':
            colunas_insert += ", IDMotivoRefugo"
            valores_placeholders += ", ?"
            params_insert.append(id_motivo_refugo)

            # Verifica se o refugo deve subtrair da produção (reclassificação)
            cursor_local.execute("SELECT SubtraiDaProducao FROM TBL_MotivoRefugo WHERE IDMotivoRefugo = ?", id_motivo_refugo)
            motivo_refugo_info = cursor_local.fetchone()
            if motivo_refugo_info and motivo_refugo_info.SubtraiDaProducao:
                logger.info(f"Refugo manual (ID Motivo: {id_motivo_refugo}) é reclassificação. Registrando estorno automático.")
                obs_estorno = f"Estorno automático por refugo manual (reclassificação). Motivo original: {observacao}"
                # Insere um evento de ESTORNO correspondente
                cursor_local.execute(f"""
                    INSERT INTO VW_EventoProducaoComCicloReal (
                        IDExecucao, IDOrdemProducao, IDMaquina, IDOperador, IDTurno, IDTipoRecurso,
                        Quantidade, TipoValor, OrigemEvento, ObsEvento, DataHoraEvento, IDTipoEvento,
                        IDOrdemOperacao, IDMotivoRefugo
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, 'ESTORNO', 'AUTOMATICO_REFUGO_MANUAL', ?, ?, ?, ?, ?)
                """, (
                    execucao_info.IDExecucao, execucao_info.IDOrdem, id_maquina, id_operador_apontamento,
                    id_turno_maquina, execucao_info.IDTipoRecurso,
                    -quantidade, # Quantidade negativa para estorno
                    obs_estorno, data_hora_evento, 2, # IDTipoEvento 2
                    execucao_info.IDOrdemOperacao, id_motivo_refugo # Inclui motivo no estorno também
                ))

        # Monta e executa a query principal de inserção
        sql_final_insert = f"INSERT INTO VW_EventoProducaoComCicloReal ({colunas_insert}) VALUES ({valores_placeholders})"
        logger.debug(f"Executando INSERT manual: {sql_final_insert} com params: {params_insert}")
        cursor_local.execute(sql_final_insert, params_insert)

        conn_local.commit() # Confirma as alterações no banco

        # Formata a quantidade para a mensagem de sucesso
        quantidade_fmt = ("%g" % quantidade).replace('.', ',')
        tipo_fmt = "peça(s) boa(s)" if tipo_valor == "BOA" else "unidade(s) de refugo"
        message_success = f'Apontamento de {quantidade_fmt} {tipo_fmt} registrado com sucesso!'
        logger.info(f"Apontamento manual registrado para máquina {id_maquina}: {quantidade} {tipo_valor}")
        return jsonify({'success': True, 'message': message_success})

    except Exception as e:
        if conn_local:
            try:
                conn_local.rollback() # Tenta reverter a transação em caso de erro
                logger.warning(f"Rollback executado para máquina {id_maquina} devido a erro no apontamento manual.")
            except Exception as rb_err:
                logger.error(f"Erro durante o rollback para máquina {id_maquina}: {rb_err}")

        # Log detalhado do erro
        import traceback
        tb_str = traceback.format_exc()
        logger.error(f"Erro CRÍTICO na rota /manual/registrar_producao para máquina {id_maquina}: {e}\n{tb_str}")

        # Mensagem genérica para o usuário
        return jsonify({'success': False, 'message': 'Erro interno no servidor ao registrar apontamento. Verifique os logs para detalhes.'}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local) # Garante que a conexão seja devolvida ao pool        

# Adicione esta rota ao seu planner_app.py

@app.route('/cadastros_manutencao')
@login_requerido
@permissao_requerida('/cadastros_manutencao') # Lembre-se de cadastrar esta permissão
def cadastros_manutencao():
    return render_template('cadastros_manutencao.html')            

# --- Função Auxiliar para Garantir o Job do OEE ---
def garantir_agendamento_oee():
    """
    Garante que o job de cálculo de OEE esteja no agendador.
    Essencial chamar após recarregar_agendamentos() ou na inicialização.
    """
    try:
        # Verifica se o job já existe para não duplicar, ou força a atualização
        # O ID deve ser o mesmo usado se você tivesse definido no scheduler.py
        scheduler.add_job(
            calcular_e_salvar_oee_periodicamente,
            'interval',
            seconds=60, # Roda a cada 60 segundos
            id='job_calculo_oee_periodico',
            replace_existing=True
        )
        logger.info("Job de cálculo periódico de OEE (re)adicionado ao agendador com sucesso.")
    except Exception as e:
        logger.error(f"Erro ao garantir agendamento do OEE: {e}", exc_info=True)            
        
# --- Rota para renderizar a página do Andon ---
@app.route('/andon')
@login_requerido
def andon():
    # Renderiza a página HTML inicial
    return render_template('andon.html')

@app.route('/api/andon_data')
def api_andon_data():
    conn_local = None
    try:
        conn_local = obter_conexao()
        
        query = """
        SELECT 
            R.IDMaquina, R.NomeMaquina, S.Nome AS NomeSetor,
            
            -- Status Atual e DATA DE INÍCIO DO STATUS
            ST.Status AS StatusAtual,
            ST.DataHoraInicio AS DataInicioStatus, 
            ISNULL(MP.Descricao, ST.ObsEvento) AS DescricaoMotivoParada,
            
            -- Dados OP
            EX.IDExecucao, EX.CodigoOrdem, EX.DataHoraInicio AS DataInicioOP,
            P.CodigoProduto, P.NomeProduto,
            OPO.NumeroOperacao, OPO.Descricao AS DescricaoOperacao,
            U.NomeOperador,
            
            -- Produção Real (OTIMIZADO - Lendo TBL_EventoProducao)
            ISNULL((SELECT SUM(Quantidade) FROM TBL_EventoProducao -- Alterado
                    WHERE IDOrdemProducao = EX.IDOrdem 
                    AND IDOrdemOperacao = EX.IDOrdemOperacao 
                    AND TipoValor IN ('BOA', 'ESTORNO')), 0) AS Produzido,

            ISNULL((SELECT SUM(Quantidade) FROM TBL_EventoProducao -- Alterado
                    WHERE IDOrdemProducao = EX.IDOrdem 
                    AND IDOrdemOperacao = EX.IDOrdemOperacao 
                    AND TipoValor = 'REFUGO'), 0) AS Refugo,
            
            ISNULL(OPO.QuantidadePlanejada, EX.QuantidadePlanejada) AS Meta,
            
            CASE 
                WHEN EX.UsarTempoCicloRecurso = 1 AND RP.TempoCicloPadraoSegundos IS NOT NULL 
                THEN RP.TempoCicloPadraoSegundos 
                ELSE P.TempoCicloSegundos 
            END AS TempoCicloSegundos,
            ISNULL(EX.FatorMultiplicacaoOrdem, 1) AS FatorMultiplicacao,

            -- Índices
            ISNULL(OEE.Disponibilidade, 0) * 100 AS DispPct,
            ISNULL(OEE.Performance, 0) * 100 AS PerfPct,
            ISNULL(OEE.Qualidade, 0) * 100 AS QualPct,
            ISNULL(OEE.OEE, 0) * 100 AS OEEPct,

            -- >>> NOVO: Contagem de Alarmes Ativos <<<
            ISNULL(AL.QtdAlarmes, 0) AS QtdAlarmes

        FROM TBL_Recurso R
        LEFT JOIN TBL_Setor S ON R.IDSetor = S.IDSetor
        
        -- 1. Status Atual (Incluindo DataHoraInicio)
        OUTER APPLY (
            SELECT TOP 1 Status, IDMotivoParada, ObsEvento, DataHoraInicio
            FROM TBL_StatusMaquina 
            WHERE IDMaquina = R.IDMaquina AND DataHoraFim IS NULL 
            ORDER BY DataHoraRegistro DESC
        ) ST
        LEFT JOIN TBL_MotivoParada MP ON ST.IDMotivoParada = MP.IDMotivoParada
        
        -- 2. OP Ativa
        OUTER APPLY (
            SELECT TOP 1 
                E.IDExecucao, E.DataHoraInicio, E.IDOperador,
                E.IDOrdem, E.IDOrdemOperacao, O.CodigoOrdem, O.IDProduto, O.QuantidadePlanejada,
                O.UsarTempoCicloRecurso, O.FatorMultiplicacaoOrdem
            FROM TBL_ExecucaoOP E
            JOIN TBL_OrdemProducao O ON E.IDOrdem = O.IDOrdem
            WHERE E.IDMaquina = R.IDMaquina AND E.Status IN ('Em Execucao', 'Em Setup')
            ORDER BY E.DataHoraInicio DESC
        ) EX
        LEFT JOIN TBL_Produto P ON EX.IDProduto = P.IDProduto
        LEFT JOIN TBL_OrdemProducao_Operacoes OPO ON EX.IDOrdemOperacao = OPO.IDOrdemOperacao
        LEFT JOIN TBL_Operador U ON EX.IDOperador = U.IDOperador
        LEFT JOIN TBL_RecursoProduto RP ON EX.IDProduto = RP.IDProduto AND R.IDMaquina = RP.IDRecurso

        -- 3. OEE
        OUTER APPLY (
            SELECT TOP 1 Disponibilidade, Performance, Qualidade, OEE
            FROM TBL_IndiceOEE 
            WHERE IDMaquina = R.IDMaquina 
            ORDER BY DataHoraCalculo DESC
        ) OEE

        -- 4. Verificar Alarmes Ativos (NOVO BLOCO)
        OUTER APPLY (
            SELECT COUNT(*) as QtdAlarmes
            FROM TBL_LogAlarmes
            WHERE IDMaquina = R.IDMaquina AND Status = 'ATIVO'
        ) AL

        WHERE R.Ativo = 1
        ORDER BY R.NomeMaquina
        """
        
        df = pd.read_sql(query, conn_local)
        andon_data = []
        agora = datetime.now()

        for _, row in df.iterrows():
            qtd_prod = float(row['Produzido'] if pd.notnull(row['Produzido']) else 0)
            meta = float(row['Meta'] if pd.notnull(row['Meta']) else 0)
            
            # Saldo: Pendente
            saldo = int(meta - qtd_prod) if meta > 0 else 0
            cor_saldo = "val-pos" if saldo <= 0 and meta > 0 else "val-neutral"

            # ETA
            eta = "--:--"
            ciclo = float(row['TempoCicloSegundos'] if pd.notnull(row['TempoCicloSegundos']) else 0)
            fator = float(row['FatorMultiplicacao'] if pd.notnull(row['FatorMultiplicacao']) else 1)
            
            if saldo > 0 and ciclo > 0:
                segundos_restantes = (saldo * ciclo) / fator / 0.85
                data_fim = agora + timedelta(seconds=segundos_restantes)
                eta = data_fim.strftime('%H:%M') if data_fim.date() == agora.date() else data_fim.strftime('%d/%m %H:%M')
            elif meta > 0 and saldo <= 0:
                eta = "Concluído"

            op_desc = f"{row['NumeroOperacao']} - {row['DescricaoOperacao'] or ''}" if row['NumeroOperacao'] else ""

            # Data de início do status para o cronômetro
            dt_inicio_status = row['DataInicioStatus']
            str_inicio_status = ""
            if pd.notnull(dt_inicio_status):
                if hasattr(dt_inicio_status, 'isoformat'):
                    str_inicio_status = dt_inicio_status.isoformat()
                else:
                    str_inicio_status = str(dt_inicio_status)

            # Lógica do Alarme
            tem_alarme = True if row['QtdAlarmes'] > 0 else False

            andon_data.append({
                'IDMaquina': row['IDMaquina'],
                'NomeMaquina': row['NomeMaquina'],
                'StatusAtual': int(row['StatusAtual']) if pd.notnull(row['StatusAtual']) else -1,
                'DataInicioStatus': str_inicio_status, 
                'DescricaoMotivoParada': row['DescricaoMotivoParada'] or '',
                'OEE': float(row['OEEPct'] if pd.notnull(row['OEEPct']) else 0),
                'Disponibilidade': float(row['DispPct'] if pd.notnull(row['DispPct']) else 0),
                'Performance': float(row['PerfPct'] if pd.notnull(row['PerfPct']) else 0),
                'Qualidade': float(row['QualPct'] if pd.notnull(row['QualPct']) else 0),
                'OrdemAtual': row['CodigoOrdem'],
                'Produto': row['NomeProduto'],
                'CodigoProduto': row['CodigoProduto'],
                'Operacao': op_desc,
                'Operador': row['NomeOperador'],
                'Produzido': int(qtd_prod),
                'Refugo': int(row['Refugo'] if pd.notnull(row['Refugo']) else 0),
                'Planejado': int(meta),
                'Progresso': (qtd_prod / meta * 100) if meta > 0 else 0,
                'Saldo': saldo,
                'CorSaldo': cor_saldo,
                'ETA': eta,
                'TemAlarme': tem_alarme # Campo adicionado
            })

        total = len(andon_data)
        rodando = sum(1 for x in andon_data if x['StatusAtual'] == 1)
        media_oee = sum(x['OEE'] for x in andon_data) / total if total > 0 else 0

        return jsonify({
            'maquinas': andon_data,
            'global': {
                'total': total,
                'rodando': rodando,
                'paradas': total - rodando,
                'oee_medio': media_oee
            }
        })

    except Exception as e:
        logger.error(f"Erro na API Andon: {e}", exc_info=True)
        return jsonify({'error': str(e)}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)
            
            ######MATERIAIS###############
# --- API para LISTAR os materiais de uma operação (para mostrar no Modal) ---
@app.route('/api/materiais_roteiro/<int:id_roteiro_operacao>')
@login_requerido
def api_materiais_roteiro(id_roteiro_operacao):
    conn = obter_conexao()
    cursor = conn.cursor()
    try:
        cursor.execute("""
            SELECT RM.IDRoteiroMaterial, MP.NomeMateriaPrima, UM.Sigla, RM.QuantidadePadrao
            FROM TBL_RoteiroOperacao_Materiais RM
            JOIN TBL_MateriaPrima MP ON RM.IDMateriaPrima = MP.IDMateriaPrima
            LEFT JOIN TBL_UnidadeMedida UM ON MP.IDUnidade = UM.IDUnidade
            WHERE RM.IDRoteiroOperacao = ?
        """, (id_roteiro_operacao,))
        
        materiais = [
            {
                "id": row.IDRoteiroMaterial, 
                "nome": row.NomeMateriaPrima, 
                "unidade": row.Sigla, 
                "qtd": row.QuantidadePadrao
            } for row in cursor.fetchall()
        ]
        return jsonify(materiais)
    finally:
        devolver_conexao(conn)
# --- ROTA ÚNICA E CORRETA PARA LISTAR MATERIAIS NO DASHBOARD ---
@app.route('/api/dashboard/materiais_instrucao/<int:id_maquina>')
@login_requerido
def api_materiais_instrucao(id_maquina):
    conn = obter_conexao()
    cursor = conn.cursor()
    try:
        # 1. Descobrir qual Operação está rodando na máquina AGORA
        cursor.execute("""
            SELECT TOP 1 E.IDOrdemOperacao
            FROM TBL_ExecucaoOP E
            WHERE E.IDMaquina = ? AND E.Status IN ('Em Execucao', 'Em Setup')
            ORDER BY E.DataHoraInicio DESC
        """, (id_maquina,))
        
        execucao = cursor.fetchone()
        
        if not execucao or not execucao.IDOrdemOperacao:
            return jsonify({'success': False, 'message': 'Nenhuma operação com roteiro ativa no momento.'})

        # 2. Buscar os materiais na tabela específica da OP (TBL_OrdemProducao_Operacoes_Materiais)
        cursor.execute("""
            SELECT 
                MP.CodigoMateriaPrima,
                MP.NomeMateriaPrima,
                UM.Sigla,
                OPM.QuantidadePlanejada
            FROM TBL_OrdemProducao_Operacoes_Materiais OPM
            JOIN TBL_MateriaPrima MP ON OPM.IDMateriaPrima = MP.IDMateriaPrima
            LEFT JOIN TBL_UnidadeMedida UM ON MP.IDUnidade = UM.IDUnidade
            WHERE OPM.IDOrdemOperacao = ?
        """, (execucao.IDOrdemOperacao,))
        
        materiais = []
        for row in cursor.fetchall():
            materiais.append({
                'codigo': row.CodigoMateriaPrima,
                'nome': row.NomeMateriaPrima,
                'unidade': row.Sigla,
                'qtd_planejada': float(row.QuantidadePlanejada)
            })
            
        return jsonify({'success': True, 'materiais': materiais})

    except Exception as e:
        logger.error(f"Erro ao buscar materiais da instrução (OP): {e}")
        return jsonify({'error': 'Erro interno ao buscar dados'}), 500
    finally:
        devolver_conexao(conn)            
 
 
@app.route('/regras_agendamento', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_turno') # Pode usar a mesma permissão de turnos
def regras_agendamento():
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()

        if request.method == 'POST':
            # --- Lógica de Salvamento ---
            id_regra = request.form.get('id_regra')
            nome = request.form.get('nome')
            hora_inicio = request.form.get('hora_inicio')
            hora_fim = request.form.get('hora_fim')
            
            # Campos de Escopo (Um dos dois deve ser preenchido)
            id_turno = request.form.get('id_turno') or None
            id_recurso = request.form.get('id_recurso') or None
            
            # Ação e Motivo
            tipo_acao = int(request.form.get('tipo_acao')) # 0=Parar, 1=Produzir
            id_motivo = request.form.get('id_motivo') or None
            
            # Prioridade Automática: Regra de Máquina (10) ganha de Regra de Turno (1)
            prioridade = 10 if id_recurso else 1
            
            if id_regra:
                cursor_local.execute("""
                    UPDATE TBL_RegraAgendamento 
                    SET NomeRegra=?, HoraInicio=?, HoraFim=?, IDTurno=?, IDRecurso=?, 
                        TipoAcao=?, IDMotivoParada=?, Prioridade=?
                    WHERE IDRegra=?
                """, (nome, hora_inicio, hora_fim, id_turno, id_recurso, tipo_acao, id_motivo, prioridade, id_regra))
                flash("Regra atualizada. A agenda será recalculada em instantes.", "success")
            else:
                cursor_local.execute("""
                    INSERT INTO TBL_RegraAgendamento 
                    (NomeRegra, HoraInicio, HoraFim, IDTurno, IDRecurso, TipoAcao, IDMotivoParada, Prioridade, Ativo)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, 1)
                """, (nome, hora_inicio, hora_fim, id_turno, id_recurso, tipo_acao, id_motivo, prioridade))
                flash("Nova regra criada. A agenda será recalculada em instantes.", "success")
            
            conn_local.commit()
            
            # DISPARA O FLATTENER EM BACKGROUND
            try:
                from flattener import consolidar_agendas_afetadas
                threading.Thread(target=consolidar_agendas_afetadas, args=(id_turno, id_recurso)).start()
            except Exception as e_thread:
                logger.error(f"Erro ao disparar flattener: {e_thread}")

            return redirect(url_for('regras_agendamento'))

        # --- Lógica de Visualização (GET) ---
        
        # 1. Busca as regras existentes com nomes amigáveis
        cursor_local.execute("""
            SELECT 
                RA.IDRegra, RA.NomeRegra, 
                FORMAT(CAST(RA.HoraInicio AS DATETIME), 'HH:mm') as HoraInicioFmt,
                FORMAT(CAST(RA.HoraFim AS DATETIME), 'HH:mm') as HoraFimFmt,
                RA.TipoAcao,
                RA.Prioridade,
                ISNULL(T.NomeTurno, 'Todos / N/A') as NomeTurno,
                ISNULL(R.NomeMaquina, 'Todas do Turno') as NomeRecurso,
                ISNULL(MP.Descricao, '-') as NomeMotivo,
                RA.IDTurno, RA.IDRecurso, RA.IDMotivoParada, RA.HoraInicio, RA.HoraFim
            FROM TBL_RegraAgendamento RA
            LEFT JOIN TBL_Turno T ON RA.IDTurno = T.IDTurno
            LEFT JOIN TBL_Recurso R ON RA.IDRecurso = R.IDMaquina
            LEFT JOIN TBL_MotivoParada MP ON RA.IDMotivoParada = MP.IDMotivoParada
            ORDER BY RA.Prioridade DESC, RA.HoraInicio ASC
        """)
        regras = cursor_local.fetchall()

        # 2. Dados para os Dropdowns
        cursor_local.execute("SELECT IDTurno, NomeTurno FROM TBL_Turno WHERE Ativo=1 ORDER BY NomeTurno")
        turnos = cursor_local.fetchall()

        cursor_local.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo=1 ORDER BY NomeMaquina")
        maquinas = cursor_local.fetchall()

        cursor_local.execute("SELECT IDMotivoParada, Descricao FROM TBL_MotivoParada WHERE Ativo=1 ORDER BY Descricao")
        motivos = cursor_local.fetchall()

        return render_template('regras_agendamento.html', 
                               regras=regras, turnos=turnos, maquinas=maquinas, motivos=motivos)

    except Exception as e:
        logger.error(f"Erro na rota regras_agendamento: {e}", exc_info=True)
        flash("Erro ao carregar regras.", "error")
        return redirect(url_for('home'))
    finally:
        if conn_local: devolver_conexao(conn_local)

@app.route('/regras_agendamento/excluir/<int:id_regra>', methods=['POST'])
@login_requerido
@permissao_requerida('/cadastro_turno')
def excluir_regra_agendamento(id_regra):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        # Busca dados antes de apagar para saber o que recalcular
        cursor_local.execute("SELECT IDTurno, IDRecurso FROM TBL_RegraAgendamento WHERE IDRegra = ?", (id_regra,))
        dados = cursor_local.fetchone()
        
        cursor_local.execute("DELETE FROM TBL_RegraAgendamento WHERE IDRegra = ?", (id_regra,))
        conn_local.commit()
        
        if dados:
            from flattener import consolidar_agendas_afetadas
            threading.Thread(target=consolidar_agendas_afetadas, args=(dados.IDTurno, dados.IDRecurso)).start()
            
        flash("Regra excluída e agenda recalculada.", "success")
    except Exception as e:
        logger.error(f"Erro ao excluir regra: {e}")
        flash("Erro ao excluir.", "error")
    finally:
        if conn_local: devolver_conexao(conn_local)
    return redirect(url_for('regras_agendamento'))
    
def _update_machine_status(conn_local, cursor_local, id_maquina, new_status, id_motivo_parada=None, obs_evento=''):
    """
    Função auxiliar para atualizar o status de uma máquina.
    VERSÃO FINAL E ROBUSTA: Atualiza o status em TBL_ExecucaoOP e TBL_OrdemProducao de forma direta.
    AGORA COM RASTREABILIDADE: Grava IDOrdem e IDOrdemOperacao no histórico de status.
    """
    timestamp = datetime.now()
    id_turno_atual = identificar_turno(conn_local, cursor_local)
    
    new_record_id = None

    # 1. Busca o contexto da produção atual (Ordem e Operação)
    # Isso garante que a parada ou o inicio de produção fiquem vinculados à OP correta
    id_ordem_contexto = None
    id_ordem_operacao_contexto = None

    try:
        cursor_local.execute("""
            SELECT TOP 1 IDOrdem, IDOrdemOperacao 
            FROM TBL_ExecucaoOP 
            WHERE IDMaquina = ? AND Status IN ('Em Execucao', 'Em Setup')
            ORDER BY DataHoraInicio DESC
        """, (id_maquina,))
        row_contexto = cursor_local.fetchone()
        if row_contexto:
            id_ordem_contexto = row_contexto.IDOrdem
            id_ordem_operacao_contexto = row_contexto.IDOrdemOperacao
    except Exception as e:
        logger.error(f"Erro ao buscar contexto da OP para status da máquina {id_maquina}: {e}")

    # 2. Busca o último status registrado para fechar (Update do DataHoraFim)
    cursor_local.execute("""
        SELECT TOP 1 IDRegistroStatus, Status, IDMotivoParada
        FROM TBL_StatusMaquina 
        WHERE IDMaquina = ? AND DataHoraFim IS NULL
        ORDER BY DataHoraRegistro DESC
    """, id_maquina)
    ultimo_status_db = cursor_local.fetchone()

    # --- INÍCIO DA LÓGICA DE ATUALIZAÇÃO DE STATUS DA OP (VERSÃO REFORÇADA) ---
    if new_status == 1 and ultimo_status_db and ultimo_status_db.Status == 0:
        cursor_local.execute("SELECT IDMotivoParada FROM TBL_MotivoParada WHERE Codigo = '03'")
        motivo_setup_row = cursor_local.fetchone()
        id_motivo_setup = motivo_setup_row.IDMotivoParada if motivo_setup_row else -1

        if ultimo_status_db.IDMotivoParada == id_motivo_setup:
            logger.info(f"Máquina {id_maquina} saindo de SETUP. Iniciando atualização de status da OP.")
            
            # Encontrar a ID da ordem que está 'Em Setup'
            cursor_local.execute("SELECT IDOrdem FROM TBL_ExecucaoOP WHERE IDMaquina = ? AND Status = 'Em Setup'", (id_maquina,))
            execucao_em_setup = cursor_local.fetchone()

            if execucao_em_setup:
                id_ordem_a_atualizar = execucao_em_setup.IDOrdem

                # Atualizar a tabela de execução
                cursor_local.execute("""
                    UPDATE TBL_ExecucaoOP 
                    SET Status = 'Em Execucao' 
                    WHERE IDOrdem = ? AND IDMaquina = ? AND Status = 'Em Setup'
                """, (id_ordem_a_atualizar, id_maquina))
                
                # Atualizar a tabela principal da ordem
                cursor_local.execute("SELECT IDStatus FROM TBL_StatusOrdemProducao WHERE NomeStatus = 'Em Execucao'")
                status_exec_row = cursor_local.fetchone()
                if status_exec_row:
                    id_status_execucao = status_exec_row.IDStatus
                    cursor_local.execute("""
                        UPDATE TBL_OrdemProducao
                        SET IDStatus = ?
                        WHERE IDOrdem = ?
                    """, (id_status_execucao, id_ordem_a_atualizar))
    # --- FIM DA LÓGICA DE ATUALIZAÇÃO ---

    # Evita duplicidade se o status for idêntico (exceto se for troca de motivo de parada)
    if ultimo_status_db and ultimo_status_db.Status == new_status:
        if (new_status == 0 and ultimo_status_db.IDMotivoParada == id_motivo_parada) or new_status == 1:
            return ultimo_status_db.IDRegistroStatus

    # Fecha o registro anterior
    if ultimo_status_db:
        cursor_local.execute("""
            UPDATE TBL_StatusMaquina 
            SET DataHoraFim = ?, DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, ?)
            WHERE IDRegistroStatus = ?
        """, timestamp, timestamp, ultimo_status_db.IDRegistroStatus)

    # Prepara o Insert do novo registro (AGORA COM IDOrdem E IDOrdemOperacao)
    sql_insert_base = "INSERT INTO TBL_StatusMaquina ({columns}) OUTPUT INSERTED.IDRegistroStatus VALUES ({placeholders})"
    
    observacao_final = obs_evento
    if new_status == 0 and id_motivo_parada:
        try:
            cursor_local.execute("SELECT Descricao FROM TBL_MotivoParada WHERE IDMotivoParada = ?", id_motivo_parada)
            motivo_row = cursor_local.fetchone()
            if motivo_row and motivo_row.Descricao:
                observacao_final = motivo_row.Descricao
                if obs_evento: observacao_final = f"{observacao_final} ({obs_evento})"
        except Exception as e:
            logger.error(f"Erro ao buscar descrição do motivo de parada {id_motivo_parada}: {e}")

    # Configuração dos parâmetros do INSERT
    if new_status == 1:
        # Status Produzindo
        columns = "IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, ObsEvento, IDOrdem, IDOrdemOperacao"
        placeholders = "?, ?, ?, ?, ?, ?, ?, ?"
        params = (id_maquina, new_status, timestamp, timestamp, id_turno_atual, observacao_final, id_ordem_contexto, id_ordem_operacao_contexto)
    else:
        # Status Parado
        columns = "IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDMotivoParada, IDTurno, ObsEvento, IDOrdem, IDOrdemOperacao"
        placeholders = "?, ?, ?, ?, ?, ?, ?, ?, ?"
        id_motivo_parada_final = id_motivo_parada or ID_MOTIVO_PARADA_AUTOMATICA
        params = (id_maquina, new_status, timestamp, timestamp, id_motivo_parada_final, id_turno_atual, observacao_final, id_ordem_contexto, id_ordem_operacao_contexto)

    # Executa o INSERT
    sql_insert_final = sql_insert_base.format(columns=columns, placeholders=placeholders)
    new_record_id = cursor_local.execute(sql_insert_final, params).fetchval()

    # Log na tabela de Eventos (Opcional: Pode adicionar IDOrdem aqui também se quiser no futuro)
    if new_status == 1:
        cursor_local.execute("INSERT INTO TBL_EventoStatus (IDMaquina, Status, DataHoraEvento, ObsEvento) VALUES (?, ?, ?, ?)", id_maquina, new_status, timestamp, observacao_final)
    else:
        cursor_local.execute("INSERT INTO TBL_EventoStatus (IDMaquina, Status, DataHoraEvento, IDMotivoParada, ObsEvento) VALUES (?, ?, ?, ?, ?)", id_maquina, new_status, timestamp, id_motivo_parada, observacao_final)

    logger.info(f"Status da máquina {id_maquina} atualizado (Novo ID: {new_record_id} | OP: {id_ordem_contexto}).")
    return new_record_id    
    
    
@app.route('/api/diagnostico_robo/<int:id_maquina>')
@login_requerido
def diagnostico_robo(id_maquina):
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        agora = datetime.now()
        relatorio = {}

        # 1. Configuração da Máquina
        cursor_local.execute("SELECT NomeMaquina, Automatico, LimiteInatividadeSegundos FROM TBL_Recurso WHERE IDMaquina = ?", id_maquina)
        maq = cursor_local.fetchone()
        relatorio['Maquina'] = {
            'Nome': maq.NomeMaquina,
            'Sensorizada (Automatico)': bool(maq.Automatico),
            'Limite Inatividade': f"{maq.LimiteInatividadeSegundos} segundos"
        }

        # 2. Status Atual Real
        cursor_local.execute("SELECT TOP 1 Status, DataHoraInicio, IDMotivoParada FROM TBL_StatusMaquina WHERE IDMaquina = ? AND DataHoraFim IS NULL ORDER BY DataHoraRegistro DESC", id_maquina)
        status = cursor_local.fetchone()
        relatorio['Status_Real_Agora'] = {
            'Status': status.Status if status else 'Sem Status',
            'Inicio': status.DataHoraInicio.strftime('%H:%M:%S') if status else '-',
            'MotivoID': status.IDMotivoParada if status else '-'
        }

        # 3. O que a Agenda Manda (Scheduler)
        cursor_local.execute("SELECT HoraInicio, HoraFim, EstadoPlanejado, OrigemRegra FROM TBL_AgendaConsolidada WHERE IDMaquina = ? AND ? BETWEEN HoraInicio AND HoraFim", (id_maquina, agora))
        agenda = cursor_local.fetchone()
        relatorio['Agenda_Consolidada_Manda'] = {
            'Horario': f"{agenda.HoraInicio.strftime('%H:%M')} as {agenda.HoraFim.strftime('%H:%M')}" if agenda else "BURACO NA AGENDA (Nenhum registro)",
            'Estado': agenda.EstadoPlanejado if agenda else 'N/A',
            'Origem': agenda.OrigemRegra if agenda else 'N/A'
        }

        # 4. Último Pulso (Supervisor)
        cursor_local.execute("SELECT TOP 1 DataHoraEvento FROM VW_EventoProducaoComCicloReal WHERE IDMaquina = ? AND TipoValor='BOA' ORDER BY DataHoraEvento DESC", id_maquina)
        pulso = cursor_local.fetchone()
        
        segundos_sem_pulso = 0
        if pulso:
            segundos_sem_pulso = (agora - pulso.DataHoraEvento).total_seconds()
        
        relatorio['Supervisor_Vê'] = {
            'Ultimo_Pulso': pulso.DataHoraEvento.strftime('%H:%M:%S') if pulso else 'Nunca',
            'Segundos_Sem_Producao': int(segundos_sem_pulso),
            'Estourou_Limite?': segundos_sem_pulso > (maq.LimiteInatividadeSegundos or 30)
        }

        # 5. Turno
        id_turno = identificar_turno_da_maquina(conn_local, cursor_local, id_maquina)
        relatorio['Turno_Detectado'] = id_turno if id_turno else "FORA DE TURNO (None)"

        # CONCLUSÃO DO DIAGNÓSTICO
        conclusao = []
        if not maq.Automatico:
            conclusao.append("ERRO: Máquina está como MANUAL (Automatico=0). Robôs ignoram.")
        
        if not agenda:
            conclusao.append("ERRO: Buraco na Agenda. Scheduler não atua. Rode o Flattener novamente.")
        elif agenda.EstadoPlanejado == 0 and status.Status == 1:
            conclusao.append(f"ERRO SCHEDULER: Agenda manda PARAR ({agenda.OrigemRegra}), mas máquina está RODANDO. Scheduler deveria ter atuado.")
        
        if maq.Automatico and status.Status == 1 and segundos_sem_pulso > (maq.LimiteInatividadeSegundos or 30):
            if agenda and agenda.EstadoPlanejado == 0:
                conclusao.append("INFO: Supervisor não parou a máquina porque a Agenda diz que é horário de parada programada (Café/Almoço). O Scheduler é quem deveria ter mudado o status.")
            else:
                conclusao.append("ERRO SUPERVISOR: Máquina estourou tempo limite e Supervisor não derrubou. Verifique logs de erro.")

        relatorio['DIAGNOSTICO_FINAL'] = conclusao

        return jsonify(relatorio)

    except Exception as e:
        return jsonify({'Erro_Diagnostico': str(e)})
    finally:
        if conn_local: devolver_conexao(conn_local) 
        
# ==============================================================================
#  MÓDULO DE INTEGRAÇÃO COM PAINEL IHM (ESP32)
#  Adicione este bloco no final do arquivo, antes do "if __name__..."
# ==============================================================================

@app.route('/api/esp32/status', methods=['GET'])
def api_esp32_status():
    machine_id = request.headers.get('X-Machine-ID', '1')
    
    # --- AQUI VOCÊ VAI FAZER UM SELECT NO BANCO DEPOIS ---
    # Por enquanto, vou simular dados mudando sozinhos
    # para você ver o ponteiro se mexendo na tela do ESP32:
    
    segundos = datetime.now().second
    eficiencia_simulada = int((segundos / 60) * 100) # Vai de 0 a 100 conforme o relógio
    
    dados = {
        "estado": "PRODUZINDO" if segundos % 2 == 0 else "PARADO",
        "op_atual": "OP-TESTE-2025",
        "meta": 1000,
        "realizado": 850 + segundos,
        "eficiencia": eficiencia_simulada
    }
    return jsonify(dados)            

@app.route('/api/esp32/motivos', methods=['GET'])
def api_esp32_motivos():
    conn_local = None
    try:
        conn_local = obter_conexao() # Usa sua função de conexão existente
        cursor_local = conn_local.cursor()
        
        # Busca apenas motivos ativos
        cursor_local.execute("SELECT IDMotivoParada, Descricao FROM TBL_MotivoParada WHERE Ativo = 1 ORDER BY Descricao")
        
        motivos = []
        for row in cursor_local.fetchall():
            # AQUI A CORREÇÃO: Chama a função de limpeza definida acima
            nome_limpo = limpar_texto_para_painel(row.Descricao)
            
            motivos.append({
                'id': row.IDMotivoParada,
                'nome': nome_limpo
            })
        
        return jsonify(motivos)

    except Exception as e:
        logger.error(f"Erro API ESP32 Motivos: {e}", exc_info=True)
        return jsonify({'erro': str(e)}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)

# --- ROTA 2: RECEBER APONTAMENTO ---
@app.route('/api/esp32/apontar', methods=['POST'])
def api_esp32_apontar():
    """
    Recebe comandos da tela touch (Iniciar, Parar).
    """
    id_maquina = request.headers.get('X-Machine-ID')
    if not id_maquina: return jsonify({'erro': 'Sem ID'}), 400
    
    data = request.get_json()
    if not data: return jsonify({'erro': 'JSON invalido'}), 400

    acao = data.get('acao') # 'iniciar', 'parar'
    id_motivo = data.get('id_motivo') 
    
    conn_local = None
    try:
        conn_local = obter_conexao()
        cursor_local = conn_local.cursor()
        
        if acao == 'iniciar':
            # Chama sua função interna de atualizar status
            # IMPORTANTE: A função _update_machine_status DEVE existir no seu código
            _update_machine_status(conn_local, cursor_local, id_maquina, 1, obs_evento="Início via Painel Touch")
            conn_local.commit()
            return jsonify({'sucesso': True, 'msg': 'Maquina Iniciada'})
            
        elif acao == 'parar':
            # Se não veio motivo, usa ID 2 (Parada não identificada)
            motivo_final = id_motivo if id_motivo else 2
            
            _update_machine_status(conn_local, cursor_local, id_maquina, 0, id_motivo_parada=motivo_final, obs_evento="Parada via Painel Touch")
            conn_local.commit()
            return jsonify({'sucesso': True, 'msg': 'Maquina Parada'})
            
        return jsonify({'erro': 'Acao desconhecida'}), 400

    except Exception as e:
        if conn_local: conn_local.rollback()
        logger.error(f"Erro API ESP32 Apontar: {e}", exc_info=True)
        return jsonify({'erro': str(e)}), 500
    finally:
        if conn_local:
            devolver_conexao(conn_local)        
            


@app.route('/api/esp32/comando', methods=['POST'])
def api_esp32_comando():
    try:
        dados = request.json
        tipo = dados.get('tipo')       # 'parada' ou 'iniciar_op'
        detalhe = dados.get('detalhe') # 'FALTA MATERIAL' ou 'OP-2025-101'
        machine_id = request.headers.get('X-Machine-ID', '1')

        print(f"--- IHM COMANDO: Máq {machine_id} enviou {tipo} -> {detalhe} ---")

        # --- GRAVANDO NO SQL SERVER ---
        conn = get_db_connection()
        cursor = conn.cursor()

        if tipo == 'parada':
            # Inserir na tabela de Apontamentos
            # Ajuste 'Apontamentos' para o nome real da sua tabela
            cursor.execute("""
                INSERT INTO Apontamentos (IdMaquina, TipoEvento, Descricao, DataHora)
                VALUES (?, 'PARADA', ?, GETDATE())
            """, (machine_id, detalhe))
            print(">> Parada gravada no banco!")

        elif tipo == 'iniciar_op':
            # Atualizar status da máquina com nova OP
            cursor.execute("""
                UPDATE EstadoMaquina 
                SET OPAtual = ?, Status = 'PRODUZINDO', DataInicio = GETDATE()
                WHERE IdMaquina = ?
            """, (detalhe, machine_id))
            print(">> Nova OP iniciada no banco!")

        conn.commit()
        conn.close()
        
        return jsonify({"status": "sucesso"})

    except Exception as e:
        print(f"ERRO AO SALVAR: {e}")
        return jsonify({"status": "erro", "msg": str(e)}), 500
    
################################################################################################################            
            
# O bloco if __name__ == '__main__' agora centraliza a inicialização de TUDO.
if __name__ == '__main__':
    try:
        logger.info("Aplicação principal iniciada. Configurando threads de background...")

        # Iniciar o thread do cliente MQTT (que usa o cliente global)
        thread_mqtt_client = threading.Thread(target=mqtt_client_thread, daemon=True)
        thread_mqtt_client.start()
        logger.info("Thread do cliente MQTT (Produtor) agendada para iniciar.")

        # Iniciar o thread de escrita do banco de dados (Consumidor)
        thread_db_writer = threading.Thread(target=mqtt_database_writer_thread, daemon=True)
        thread_db_writer.start()
        logger.info("Thread de escrita MQTT no BD (Consumidor) agendada para iniciar.")

        # Iniciar o agendador de turnos
        try:
            iniciar_agendador_de_turnos()
            
            # ### <<< ADICIONADO AQUI: Inicia o OEE junto com o sistema >>> ###
            garantir_agendamento_oee() 
            # ###############################################################
            
        except Exception as e:
            logger.critical(f"FALHA AO INICIAR O AGENDADOR DE TURNOS: {e}", exc_info=True)

        # Iniciar os outros threads de verificação
        thread_inatividade = threading.Thread(target=verificar_inatividade_periodicamente, daemon=True)
        thread_inatividade.start()
        logger.info("Thread de verificação de inatividade agendada para iniciar.")

        thread_limpeza = threading.Thread(target=limpar_registros_duplicados_periodicamente, daemon=True)
        thread_limpeza.start()
        logger.info("Thread de limpeza de registros duplicados agendada para iniciar.")
        
        # Qualidade (inspeçao pendente)
        thread_qualidade = threading.Thread(target=gerar_inspecoes_pendentes_thread, daemon=True)
        thread_qualidade.start()
        logger.info("Thread do Robô de Inspeções Pendentes agendada para iniciar.")

        # Iniciar o buffer agrupado (para gravação de produção consolidada)
        start_buffer_timer()

        # Agora, inicie o servidor Flask.
        logger.info("Iniciando o servidor Flask...")
        app.run(host='0.0.0.0', port=5003, debug=False, use_reloader=False, threaded=True)

    except Exception as e:
        logger.critical(f"Erro fatal na inicialização da aplicação: {e}", exc_info=True)
        input("Pressione Enter para encerrar a aplicação...")