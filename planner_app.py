from flask import Flask, render_template, request, redirect, url_for, jsonify, session
import pyodbc
import json
import sys
from datetime import datetime, timedelta
from functools import wraps
from collections import defaultdict
import threading
import io
import time
import logging # Nova importação para logging

# Configurar logging para a aplicação
logging.basicConfig(level=logging.INFO,
                    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
                    handlers=[
                        logging.FileHandler("esp32_monitor.log", encoding='utf-8'), # Adicionado encoding
                        logging.StreamHandler(sys.stdout) # Usar sys.stdout para melhor controle
                    ])
logger = logging.getLogger(__name__)

# Forçar a codificação UTF-8 para a saída padrão e de erro do console
# Coloque estas duas linhas logo abaixo das importações, antes de qualquer outra lógica
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8')

app = Flask(__name__)
app.secret_key = 'sua_chave_secreta_segura'

# Conexão com SQL Server Express (existente no seu arquivo)
conn = pyodbc.connect(
    'DRIVER={ODBC Driver 17 for SQL Server};'
    'SERVER=192.168.1.110;'
    'DATABASE=PLN_PRD;'
    'UID=sa;' # Substitua pelo seu usuário
    'PWD=planner123;' # Substitua pela sua senha
)
cursor = conn.cursor()
cursor = conn.cursor() # Linha duplicada no original, mantida como está.

# Buffer global e lock (existente no seu arquivo)
buffer_agregado = defaultdict(int)
lock = threading.Lock()

# Função existente no seu arquivo
def forcar_gravacao_consolidada(chave):
    with lock:
        quantidade = buffer_agregado.get(chave, 0)
        if quantidade > 0:
            try:
                cursor.execute("""
                    INSERT INTO TBL_EventoProducao (
                        IDExecucao, IDRecurso, IDTipoRecurso, IDOrdemProducao,
                        IDTurno, IDOperador, IDTipoEvento, Quantidade,
                        TipoValor, OrigemEvento, DataHoraEvento
                    )
                    VALUES (?, ?, ?, ?, ?, ?, 1, ?, 'BOA', 'AUTOMATICO', GETDATE())
                """, (*chave, quantidade))
                conn.commit()
                buffer_agregado.pop(chave, None)
                logger.info(f"⚠️ Produção consolidada gravada por evento externo — chave: {chave}")
            except Exception as e:
                logger.error(f"❌ Erro ao gravar consolidado: {e}")

# Função existente no seu arquivo
def gravar_buffer_agrupado():
    global buffer_agregado

    turno_atual = identificar_turno()

    for chave in list(buffer_agregado.keys()):
        id_execucao, id_maquina, id_tipo_recurso, id_ordem, id_turno_chave, id_operador = chave

        if id_turno_chave != turno_atual:
            # Força gravação da produção do turno anterior
            forcar_gravacao_consolidada(chave)

            # Fecha o status atual
            cursor.execute("""
                UPDATE TBL_StatusMaquina
                SET DataHoraFim = GETDATE(), 
                    DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, GETDATE())
                WHERE IDMaquina = ? AND DataHoraFim IS NULL
            """, (id_maquina,))

            # Registra status especial de virada de turno
            cursor.execute("""
                INSERT INTO TBL_StatusMaquina 
                (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, IDMotivoParada, DescricaoStatus)
                VALUES (?, 99, GETDATE(), GETDATE(), ?, 99, 'Virada de Turno')
            """, (id_maquina, turno_atual))

            conn.commit()

    threading.Timer(300.0, gravar_buffer_agrupado).start()  # a cada 5 minutos

    with lock:
        if buffer_agregado:
            logger.info(f"🔄 Gravando {len(buffer_agregado)} registros consolidados no banco...")

            for chave, dados in buffer_agregado.items():
                (
                    id_execucao, id_maquina, id_tipo_recurso,
                    id_ordem, id_turno, id_operador
                ) = chave

                quantidade = dados.get('quantidade', 0)
                hora_inicial = dados.get('hora_inicial', datetime.now())
                hora_final = datetime.now()

                try:
                    cursor.execute("""
                        INSERT INTO TBL_EventoProducao (
                            IDExecucao, IDRecurso, IDTipoRecurso, IDOrdemProducao,
                            IDTurno, IDOperador, IDTipoEvento, Quantidade,
                            TipoValor, OrigemEvento, DataHoraEvento,
                            HoraInicialReal, HoraFinalReal
                        )
                        VALUES (?, ?, ?, ?, ?, ?, 1, ?, 'BOA', 'AUTOMATICO', ?, ?, ?)
                    """, (
                        id_execucao, id_maquina, id_tipo_recurso,
                        id_ordem, id_turno, id_operador, quantidade,
                        hora_final, hora_inicial, hora_final
                    ))
                except Exception as e:
                    logger.error(f"❌ Erro ao gravar linha consolidada: {e}")

            conn.commit()
            buffer_agregado.clear()

# Função existente no seu arquivo
def identificar_turno():
    agora = datetime.now().time()
    hoje = datetime.now().date()

    cursor.execute("SELECT IDTurno, HoraInicio, HoraFim FROM TBL_Turno WHERE Ativo = 1")
    turnos = cursor.fetchall()

    for turno in turnos:
        hora_inicio = turno.HoraInicio
        hora_fim = turno.HoraFim

        if hora_inicio < hora_fim:
            # Turno normal (ex: 06:00 às 14:00)
            if hora_inicio <= agora < hora_fim:
                return turno.IDTurno
        else:
            # Turno que passa da meia-noite (ex: 22:00 às 06:00)
            if agora >= hora_inicio or agora < hora_fim:
                return turno.IDTurno
              
    return None  # Nenhum turno encontrado
    
gravar_buffer_agrupado()      

  
# Decoradores (existente no seu arquivo)
def login_requerido(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'usuario_id' not in session:
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function
    
def permissao_requerida(rota):
    def decorator(f):
        @wraps(f)
        def wrapped(*args, **kwargs):
            if session.get('usuario_grupo') == 1:
                return f(*args, **kwargs)
            permissao = session.get('permissao', [])
            if rota not in permissao:
                return "Acesso negado. Você não tem permissão para acessar esta página.", 403
            return f(*args, **kwargs)
        return wrapped
    return decorator

def somente_admin(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        id_admin = 1  
        if session.get('usuario_grupo') != id_admin:
            return "Acesso restrito ao administrador.", 403
        return f(*args, **kwargs)
    return decorated_function
    
# Rotas de Login/Logout/Home (existente no seu arquivo)
@app.route('/login', methods=['GET', 'POST'])
def login():
    if request.method == 'POST':
        codigo = request.form['codigo']
        senha = request.form['senha']

        cursor.execute("""
            SELECT TBL_Usuario.IDUsuario, TBL_Usuario.NomeUsuario, TBL_Usuario.IDGrupo, TBL_GrupoUsuario.NomeGrupo
            FROM TBL_Usuario
            JOIN TBL_GrupoUsuario ON TBL_Usuario.IDGrupo = TBL_GrupoUsuario.IDGrupo
            WHERE CodigoUsuario = ? AND Senha = ?
        """, (codigo, senha))
        usuario = cursor.fetchone()

        if usuario:
            session['usuario_id'] = usuario.IDUsuario
            session['usuario_nome'] = usuario.NomeUsuario
            session['grupo'] = usuario.NomeGrupo  # isso resolve o problema no HTML
            session['usuario_grupo'] = usuario.IDGrupo
            # Carrega permissões do grupo
            cursor.execute("""
                SELECT Rota FROM TBL_PermissaoGrupo
                WHERE IDGrupo = ? AND PodeAcessar = 1
            """, (usuario.IDGrupo,))
            permissao = [row.Rota for row in cursor.fetchall()]
            session['permissao'] = permissao

            return redirect(url_for('home'))
        else:
            return render_template('login.html', erro='Credenciais inválidas')

    return render_template('login.html')

@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for('login'))
    
@app.route('/home')
@login_requerido
def home():
    return render_template('home.html')

# Cadastro de Grupo de Usuário (existente no seu arquivo)
@app.route('/cadastro_grupo_usuario', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_grupo_usuario')
def cadastro_grupo():
    if request.method == 'POST':
        nome = request.form['nome']
        codigo = request.form['codigo']
        ativo = 1 if request.form.get('ativo') == 'on' else 0

        cursor.execute("""
            INSERT INTO TBL_GrupoUsuario (NomeGrupo, CodigoGrupo, Ativo)
            VALUES (?, ?, ?)
        """, (nome, codigo, ativo))
        conn.commit()
        return redirect(url_for('cadastro_grupo_usuario'))

    # Buscar todos os grupos
    cursor.execute("SELECT * FROM TBL_GrupoUsuario")
    grupos = cursor.fetchall()

    # Buscar todas as permissões distintas
    cursor.execute("SELECT DISTINCT Rota FROM TBL_PermissaoGrupo WHERE Rota IS NOT NULL")
    permissao = [row.Rota for row in cursor.fetchall()]

    # Buscar permissões liberadas por grupo
    cursor.execute("SELECT IDGrupo, Rota FROM TBL_PermissaoGrupo WHERE PodeAcessar = 1")
    rows = cursor.fetchall()

    permissao_grupo = {}
    for row in rows:
        id_grupo = row.IDGrupo
        if id_grupo not in permissao_grupo:
            permissao_grupo[id_grupo] = []
        permissao_grupo[id_grupo].append(row.Rota)

    return render_template('cadastro_grupo_usuario.html', grupos=grupos, permissao=permissao, permissao_grupo=permissao_grupo)

# Editar Grupo (existente no seu arquivo)
@app.route('/editar_grupo', methods=['POST'])
@login_requerido
@permissao_requerida('/cadastro_grupo_usuario')
def editar_grupo():
    id_grupo = request.form['id_grupo']
    permissoes_liberadas = request.form.getlist('permissao')
    novas_permissoes = request.form.get('novas_permissoes')

    if novas_permissoes:
        import json
        novas_permissoes = json.loads(novas_permissoes)
    else:
        novas_permissoes = []

    # Primeiro, adicionar novas permissões se ainda não existirem
    for nova in novas_permissoes:
        cursor.execute(
            "SELECT COUNT(*) AS qtd FROM TBL_PermissaoGrupo WHERE IDGrupo = ? AND Rota = ?", 
            (id_grupo, nova)
        )
        qtd = cursor.fetchone().qtd
        if qtd == 0:
            cursor.execute(
                "INSERT INTO TBL_PermissaoGrupo (IDGrupo, Rota, PodeAcessar) VALUES (?, ?, 0)", 
                (id_grupo, nova)
            )
            conn.commit()

    # Agora, resetar todas permissões do grupo para 0
    cursor.execute(
        "UPDATE TBL_PermissaoGrupo SET PodeAcessar = 0 WHERE IDGrupo = ?", 
        (id_grupo,)
    )
    conn.commit()

    # Depois, ativar somente as permissões que ficaram no lado liberadas
    for rota in permissoes_liberadas:
        cursor.execute(
            """
            UPDATE TBL_PermissaoGrupo
            SET PodeAcessar = 1
            WHERE IDGrupo = ? AND Rota = ?
            """,
            (id_grupo, rota)
        )
    conn.commit()

    return redirect(url_for('cadastro_grupo_usuario'))
    
# Permissões (existente no seu arquivo)
@app.route('/permissoes', methods=['GET', 'POST'])
def permissoes():
    if request.method == 'POST':
        id_grupo = request.form['id_grupo']
        permissoes = request.form.getlist('permissoes[]')
        novas_permissoes = json.loads(request.form['novasPermissoes'])

        # Cadastra novas permissões, se não existirem
        for p in novas_permissoes:
            cursor.execute("""
                IF NOT EXISTS (SELECT 1 FROM TBL_PermissaoGrupo WHERE Rota = ?)
                INSERT INTO TBL_PermissaoGrupo (IDGrupo, Rota, PodeAcessar)
                VALUES (0, ?, 0)
            """, p, p)

        # Limpa permissões anteriores do grupo
        cursor.execute("DELETE FROM TBL_PermissaoGrupo WHERE IDGrupo = ?", id_grupo)

        # Salva as permissões liberadas
        for p in permissoes:
            cursor.execute("""
                INSERT INTO TBL_PermissaoGrupo (IDGrupo, Rota, PodeAcessar)
                VALUES (?, ?, 1)
            """, id_grupo, p)

        conn.commit()

    # Consulta de grupos e permissões
    cursor.execute("SELECT IDGrupo, NomeGrupo FROM TBL_GrupoUsuario")
    grupos = cursor.fetchall()

    cursor.execute("SELECT DISTINCT Rota FROM TBL_PermissaoGrupo WHERE Rota IS NOT NULL")
    permissoes = [row.Rota for row in cursor.fetchall()]

    cursor.execute("SELECT IDGrupo, Rota FROM TBL_PermissaoGrupo WHERE PodeAcessar = 1")
    raw = cursor.fetchall()

    permissao_grupo = {}
    for row in raw:
        permissao_grupo.setdefault(row.IDGrupo, []).append(row.Rota)

    return render_template('permissoes.html',
                           grupos=grupos,
                           permissoes=permissoes,
                           permissao_grupo=permissao_grupo)

# Cadastro de Usuário (existente no seu arquivo)
@app.route('/cadastro_usuario', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_usuario')
def cadastro_usuario():
    if request.method == 'POST':
        id_usuario = request.form.get('id_usuario')
        nome = request.form['nome']
        registro = request.form['registro']
        codigo = request.form['codigo']
        senha = request.form['senha']
        grupo = request.form['grupo']
        ativo = 1 if request.form.get('ativo') == 'on' else 0
        operador_flag = request.form.get('tambem_operador') == 'on'

        if id_usuario:
            # Atualização
            cursor.execute("""
                UPDATE TBL_Usuario
                SET NomeUsuario = ?, RegistroFuncional = ?, CodigoUsuario = ?, Senha = ?, IDGrupo = ?, Ativo = ?
                WHERE IDUsuario = ?
            """, nome, registro, codigo, senha, grupo, ativo, id_usuario)

            cursor.execute("DELETE FROM TBL_Operador WHERE IDUsuario = ?", id_usuario)

            if operador_flag:
                cursor.execute("""
                    INSERT INTO TBL_Operador (IDUsuario, NomeOperador, Ativo)
                    VALUES (?, ?, ?)
                """, id_usuario, nome, ativo)
        else:
            # Novo cadastro
            cursor.execute("""
                INSERT INTO TBL_Usuario (NomeUsuario, RegistroFuncional, CodigoUsuario, Senha, IDGrupo, Ativo)
                VALUES (?, ?, ?, ?, ?, ?)
            """, nome, registro, codigo, senha, grupo, ativo)

            cursor.execute("SELECT SCOPE_IDENTITY()")
            novo_id = cursor.fetchone()[0]

            if operador_flag:
                cursor.execute("""
                    INSERT INTO TBL_Operador (IDUsuario, NomeOperador, Ativo)
                    VALUES (?, ?, ?)
                """, novo_id, nome, ativo)

        conn.commit()
        return redirect(url_for('cadastro_usuario'))

    cursor.execute("SELECT IDGrupo, NomeGrupo FROM TBL_GrupoUsuario")
    grupos = cursor.fetchall()

    cursor.execute("SELECT IDUsuario FROM TBL_Operador")
    ids_usuarios_operadores = [row.IDUsuario for row in cursor.fetchall()]

    cursor.execute("""
        SELECT U.IDUsuario, U.NomeUsuario, U.RegistroFuncional, U.CodigoUsuario, U.Senha, U.Ativo, 
               G.NomeGrupo, G.IDGrupo
        FROM TBL_Usuario U
        LEFT JOIN TBL_GrupoUsuario G ON U.IDGrupo = G.IDGrupo
        ORDER BY U.NomeUsuario
    """)
    usuarios = cursor.fetchall()

    id_edicao = request.args.get('id')
    usuario_editar = None
    if id_edicao:
        cursor.execute("SELECT * FROM TBL_Usuario WHERE IDUsuario = ?", id_edicao)
        usuario_editar = cursor.fetchone()

    return render_template('cadastro_usuario.html',
                       usuarios=usuarios,
                       grupos=grupos,
                       usuario_editar=usuario_editar,
                       ids_usuarios_operadores=ids_usuarios_operadores)

# Cadastro de Produto (existente no seu arquivo)
@app.route('/cadastro_produto', methods=['GET', 'POST'])
def cadastro_produto():
    if request.method == 'POST':
        codigo = request.form.get('codigo')
        nome = request.form.get('nome')
        descricao = request.form.get('descricao')
        tempo_ciclo = request.form.get('tempo_ciclo')
        fator = request.form.get('fator')
        unidades_por_caixa = request.form.get('unidades_por_caixa')  # ⚠ CORRETO com underscore!
        id_unidade = request.form.get('unidade')

        # Novo campo Habilitado
        habilitado = 1 if request.form.get('habilitado') == 'on' else 0

        # Tratamento para evitar valores nulos
        if not unidades_por_caixa:
            unidades_por_caixa = 1  # Valor padrão mínimo

        cursor.execute("""
            INSERT INTO TBL_Produto 
            (CodigoProduto, NomeProduto, Descricao, TempoCicloSegundos, FatorMultiplicacao, UnidadesporCaixa, IDUnidade, Habilitado)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """, (codigo, nome, descricao, tempo_ciclo, fator, unidades_por_caixa, id_unidade, habilitado))
        conn.commit()

        return redirect(url_for('cadastro_produto'))

    # Carregar unidades para o dropdown
    cursor.execute("SELECT IDUnidade, Sigla, NomeUnidade FROM TBL_UnidadeMedida")
    unidades = cursor.fetchall()

    return render_template('cadastro_produto.html', unidades=unidades)

# Consulta de Produtos (existente no seu arquivo)
@app.route('/consulta_produtos', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/consulta_produtos')
def consulta_produtos():
    if request.method == 'POST':
        # Contar quantos produtos foram enviados (conta quantos id_produto_X vieram no POST)
        indices = []
        for key in request.form.keys():
            if key.startswith('id_produto_'):
                idx = key.split('_')[-1]
                indices.append(idx)

        for idx in indices:
            id_produto = request.form.get(f'id_produto_{idx}')
            codigo = request.form.get(f'codigo_{idx}')
            nome = request.form.get(f'nome_{idx}')
            descricao = request.form.get(f'descricao_{idx}')
            tempo_ciclo = request.form.get(f'tempo_ciclo_{idx}')
            fator = request.form.get(f'fator_{idx}')
            unidade = request.form.get(f'unidade_{idx}')
            unidades_por_caixa = request.form.get(f'unidades_por_caixa_{idx}', 1)

            cursor.execute("""
                UPDATE TBL_Produto
                SET CodigoProduto = ?, NomeProduto = ?, Descricao = ?, TempoCicloSegundos = ?, 
                    FatorMultiplicacao = ?, IDUnidade = ?, UnidadesporCaixa = ?
                WHERE IDProduto = ?
            """, codigo, nome, descricao, tempo_ciclo, fator, unidade, unidades_por_caixa, id_produto)

        conn.commit()
        return redirect(url_for('dashboard'))  # Salva e volta para o dashboard

    # 🔥 Carrega os produtos já com UnidadesporCaixa e Habilitado
    cursor.execute("""
        SELECT p.IDProduto, p.CodigoProduto, p.NomeProduto, p.Descricao, p.TempoCicloSegundos, 
               p.FatorMultiplicacao, p.IDUnidade, p.UnidadesporCaixa, p.Habilitado, u.Sigla
        FROM TBL_Produto p
        LEFT JOIN TBL_UnidadeMedida u ON p.IDUnidade = u.IDUnidade
    """)
    produtos = cursor.fetchall()

    cursor.execute("""
        SELECT IDUnidade, NomeUnidade, Sigla
        FROM TBL_UnidadeMedida
    """)
    unidades = cursor.fetchall()

    return render_template('consulta_produtos.html', produtos=produtos, unidades=unidades)
    
# Alterar Status Produto (existente no seu arquivo)
@app.route('/alterar_status_produto/<int:id_produto>/<int:status>')
def alterar_status_produto(id_produto, status):
    cursor.execute("""
        UPDATE TBL_Produto
        SET Habilitado = ?
        WHERE IDProduto = ?
    """, (status, id_produto))
    conn.commit()
    return redirect(url_for('consulta_produtos'))

# Cadastro de Recurso (existente no seu arquivo)
@app.route('/cadastro_recurso', methods=['GET', 'POST'])
def cadastro_recurso():
    id_edicao = request.args.get('id')
    recurso_editar = None

    if request.method == 'POST':
        nome = request.form['nome']
        codigo = request.form['codigo']
        tipo = request.form['tipo']
        id_setor = request.form.get('setor')
        ativo = 1 if 'ativo' in request.form else 0
        id_recurso = request.form.get('id_recurso')
        
        # Novos campos para as metas de KPI
        meta_oee = request.form.get('meta_oee', 85)  # Valor padrão de 85% se não for fornecido
        meta_qualidade = request.form.get('meta_qualidade', 95)  # Valor padrão de 95% se não for fornecido
        meta_disponibilidade = request.form.get('meta_disponibilidade', 90)  # Valor padrão de 90% se não for fornecido
        meta_performance = request.form.get('meta_performance', 90)  # Valor padrão de 90% se não for fornecido
        
        # Converter para float e garantir que são números válidos
        try:
            meta_oee = float(meta_oee)
            meta_qualidade = float(meta_qualidade)
            meta_disponibilidade = float(meta_disponibilidade)
            meta_performance = float(meta_performance)
        except ValueError:
            # Se houver erro na conversão, usar valores padrão
            meta_oee = 85.0
            meta_qualidade = 95.0
            meta_disponibilidade = 90.0
            meta_performance = 90.0

        if id_recurso:
            cursor.execute("""
                UPDATE TBL_Recurso
                SET NomeMaquina = ?, CodigoInterno = ?, IDTipo = ?, IDSetor = ?, Ativo = ?,
                    MetaOEE = ?, MetaQualidade = ?, MetaDisponibilidade = ?, MetaPerformance = ?
                WHERE IDMaquina = ?
            """, nome, codigo, tipo, id_setor, ativo, 
                meta_oee, meta_qualidade, meta_disponibilidade, meta_performance,
                id_recurso)
        else:
            cursor.execute("""
                INSERT INTO TBL_Recurso 
                (NomeMaquina, CodigoInterno, IDTipo, IDSetor, Ativo, 
                 MetaOEE, MetaQualidade, MetaDisponibilidade, MetaPerformance)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, nome, codigo, tipo, id_setor, ativo,
                meta_oee, meta_qualidade, meta_disponibilidade, meta_performance)

        conn.commit()
        return redirect(url_for('cadastro_recurso'))

    if id_edicao:
        cursor.execute("SELECT * FROM TBL_Recurso WHERE IDMaquina = ?", id_edicao)
        recurso_editar = cursor.fetchone()

    # Consulta atualizada para incluir informações do setor
    cursor.execute("""
        SELECT R.*, T.NomeTipo, S.Nome AS NomeSetor
        FROM TBL_Recurso R
        LEFT JOIN TBL_TipoRecurso T ON R.IDTipo = T.IDTipo
        LEFT JOIN TBL_Setor S ON R.IDSetor = S.IDSetor
    """)
    recursos = cursor.fetchall()

    cursor.execute("SELECT * FROM TBL_TipoRecurso")
    tipos = cursor.fetchall()

    # Consulta para obter os setores disponíveis
    cursor.execute("SELECT IDSetor, Nome, Codigo FROM TBL_Setor WHERE Ativo = 1 ORDER BY Nome")
    setores = cursor.fetchall()

    return render_template(
        'cadastro_recurso.html',
        recurso_editar=recurso_editar,
        recursos=recursos,
        tipos=tipos,
        setores=setores
    )

# --- INÍCIO DAS ROTAS NOVAS/MODIFICADAS PARA INTEGRAÇÃO COM ESP32 ---

# Rota modificada para status_maquina para usar tabelas existentes
@app.route('/status_maquina', methods=['POST'])
def status_maquina():
    try:
        data = request.get_json()
        logger.info(f"Dados recebidos em /status_maquina: {data}")
        
        # Extrair dados do JSON
        id_maquina = data.get('id_maquina')
        novo_status = data.get('status')  # 0 ou 1
        origem = data.get('origem', 'ESP32')
        
        # Validação básica
        if id_maquina is None:
            return jsonify({"status": "error", "message": "ID da máquina não fornecido"}), 400
            
        if novo_status is None:
            return jsonify({"status": "error", "message": "Status não fornecido"}), 400
        
        # Converter para inteiro se necessário
        if isinstance(novo_status, str):
            novo_status = int(novo_status)
            
        # Obter timestamp atual
        timestamp = datetime.now()
        
        # Verificar se a máquina existe
        cursor.execute("SELECT IDMaquina FROM TBL_Recurso WHERE IDMaquina = ?", id_maquina)
        maquina = cursor.fetchone()
        
        if not maquina:
            return jsonify({"status": "error", "message": f"Máquina com ID {id_maquina} não encontrada"}), 404
        
        # Atualizar o status do dispositivo ESP32 (se existir)
        cursor.execute("""
            UPDATE PLN_PRD.dbo.TBL_DispositivoESP32 
            SET UltimaConexao = ?, Status = 1 
            WHERE IDMaquina = ?
        """, timestamp, id_maquina)
        # Nota: Se TBL_DispositivoESP32 não tiver uma entrada para esta máquina, este UPDATE não fará nada.
        # Considere adicionar um INSERT se não existir, ou garantir que os dispositivos sejam pré-registrados.
        
        # Identificar o turno atual
        id_turno_atual = identificar_turno()
        
        # Verificar o último status registrado para esta máquina
        cursor.execute("""
            SELECT TOP 1 IDStatus, Status, DataHoraInicio 
            FROM TBL_StatusMaquina 
            WHERE IDMaquina = ? 
            ORDER BY DataHoraRegistro DESC
        """, id_maquina)
        
        ultimo_status_db = cursor.fetchone()
        
        # Determinar se precisamos fechar o status anterior e criar um novo
        # Condição: Não há status anterior OU o status anterior é diferente do novo status
        if not ultimo_status_db or ultimo_status_db.Status != novo_status:
            # Se houver um status anterior, fechá-lo
            if ultimo_status_db:
                cursor.execute("""
                    UPDATE TBL_StatusMaquina 
                    SET DataHoraFim = ?, 
                        DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, ?)
                    WHERE IDStatus = ?
                """, timestamp, timestamp, ultimo_status_db.IDStatus)
            
            # Descrição do status
            desc_status = "Em Execução" if novo_status == 1 else "Parada"
            
            # Inserir o novo status na TBL_StatusMaquina
            cursor.execute("""
                INSERT INTO TBL_StatusMaquina 
                (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, ObsEvento, DescricaoStatus) 
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """, id_maquina, novo_status, timestamp, timestamp, id_turno_atual, f"Status atualizado via {origem}", desc_status)
            
            # Inserir no histórico de eventos (TBL_EventoStatus)
            # Nota: TBL_EventoStatus tem IDMotivoParada. Usando NULL por enquanto, ou um motivo padrão.
            id_motivo_parada = None # Padrão para NULL
            if novo_status == 0: # Se a máquina está parando, tenta encontrar um motivo padrão 'parada não identificada'
                cursor.execute("SELECT TOP 1 IDMotivoParada FROM TBL_MotivoParada WHERE Descricao LIKE '%Não Identificada%' OR Descricao LIKE '%Sem Motivo%'")
                motivo_row = cursor.fetchone()
                if motivo_row:
                    id_motivo_parada = motivo_row.IDMotivoParada

            cursor.execute("""
                INSERT INTO TBL_EventoStatus 
                (IDMaquina, Status, DataHoraEvento, IDMotivoParada, ObsEvento) 
                VALUES (?, ?, ?, ?, ?)
            """, id_maquina, novo_status, timestamp, id_motivo_parada, f"Status atualizado via {origem}")
            
            logger.info(f"Status atualizado: Máquina {id_maquina} agora está {'ativa' if novo_status == 1 else 'parada'}")
        else:
            logger.info(f"Status não alterado: Máquina {id_maquina} continua {'ativa' if novo_status == 1 else 'parada'}")
        
        conn.commit()
        
        return jsonify({
            "status": "success", 
            "message": f"Status da máquina {id_maquina} atualizado para {'ativa' if novo_status == 1 else 'parada'}",
            "timestamp": timestamp.isoformat()
        })
        
    except Exception as e:
        logger.error(f"Erro ao atualizar status: {str(e)}", exc_info=True)
        return jsonify({"status": "error", "message": str(e)}), 500

# Rota modificada para registrar_pulso para usar tabelas existentes
@app.route('/registrar_pulso', methods=['POST'])
def registrar_pulso():
    try:
        data = request.get_json()
        logger.info(f"Dados recebidos em /registrar_pulso: {data}")
        
        # Extrair dados do JSON
        id_maquina = data.get('id_maquina')
        pulsos = int(data.get('pulsos', 1))
        origem = data.get('origem', 'ESP32')
        
        # Validação básica
        if not id_maquina:
            return jsonify({"status": "error", "message": "ID da máquina não fornecido"}), 400
            
        # Obter timestamp atual
        timestamp = datetime.now()
        
        # Verificar se a máquina existe
        cursor.execute("SELECT IDMaquina FROM TBL_Recurso WHERE IDMaquina = ?", id_maquina)
        maquina = cursor.fetchone()
        
        if not maquina:
            return jsonify({"status": "error", "message": f"Máquina com ID {id_maquina} não encontrada"}), 404
        
        # Atualizar o status do dispositivo ESP32 (se existir)
        cursor.execute("""
            UPDATE PLN_PRD.dbo.TBL_DispositivoESP32 
            SET UltimaConexao = ?, Status = 1 
            WHERE IDMaquina = ?
        """, timestamp, id_maquina)
        
        # Identificar o turno atual
        id_turno_atual = identificar_turno()

        # Verificar se há uma execução de OP ativa para esta máquina
        # Precisamos buscar todos os campos necessários para TBL_EventoProducao
        cursor.execute("""
            SELECT TOP 1 
                E.IDExecucao, E.IDOrdem, E.IDOperador, R.IDTipo, O.IDProduto
            FROM TBL_ExecucaoOP E
            JOIN TBL_Recurso R ON R.IDMaquina = E.IDMaquina
            JOIN TBL_OrdemProducao O ON O.IDOrdem = E.IDOrdem
            WHERE E.IDMaquina = ? AND E.Status = 'Em Execucao'
            ORDER BY E.DataHoraInicio DESC
        """, id_maquina)
        
        execucao_info = cursor.fetchone()
        
        if execucao_info:
            id_execucao = execucao_info.IDExecucao
            id_ordem_producao = execucao_info.IDOrdem
            id_operador = execucao_info.IDOperador
            id_tipo_recurso = execucao_info.IDTipo # Do TBL_Recurso
            id_produto = execucao_info.IDProduto # Do TBL_OrdemProducao

            # IDTipoEvento para produção (assumindo 1 para 'BOA' do seu código existente)
            id_tipo_evento_producao = 1 
            
            # Registrar o pulso como evento de produção
            cursor.execute("""
                INSERT INTO TBL_EventoProducao 
                (IDExecucao, IDTipoEvento, Quantidade, DataHoraEvento, IDMaquina, 
                 IDOrdemProducao, IDTurno, IDOperador, TipoValor, OrigemEvento, IDTipoRecurso) 
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, 'BOA', ?, ?)
            """, id_execucao, id_tipo_evento_producao, pulsos, timestamp, id_maquina, 
                 id_ordem_producao, id_turno_atual, id_operador, origem, id_tipo_recurso)
            
            # Atualizar o contador de produção na execução
            cursor.execute("""
                UPDATE TBL_ExecucaoOP 
                SET QuantidadeProduzida = ISNULL(QuantidadeProduzida, 0) + ? 
                WHERE IDExecucao = ?
            """, pulsos, id_execucao)
            
            logger.info(f"Pulso registrado: Máquina {id_maquina}, {pulsos} pulsos, execução {id_execucao}")
        else:
            # Se não há execução ativa, ainda podemos registrar o pulso, mas sem vincular a uma OP
            # Precisamos obter IDTipoRecurso do TBL_Recurso
            cursor.execute("SELECT IDTipo FROM TBL_Recurso WHERE IDMaquina = ?", id_maquina)
            recurso_tipo = cursor.fetchone()
            id_tipo_recurso = recurso_tipo.IDTipo if recurso_tipo else None

            # IDTipoEvento para produção (assumindo 1 para 'BOA')
            id_tipo_evento_producao = 1 

            cursor.execute("""
                INSERT INTO TBL_EventoProducao 
                (IDTipoEvento, Quantidade, DataHoraEvento, IDMaquina, 
                 IDTurno, TipoValor, OrigemEvento, IDTipoRecurso) 
                VALUES (?, ?, ?, ?, ?, 'BOA', ?, ?)
            """, id_tipo_evento_producao, pulsos, timestamp, id_maquina, 
                 id_turno_atual, origem, id_tipo_recurso)
            logger.warning(f"Pulso recebido para máquina {id_maquina}, mas não há execução ativa. Registrado sem vínculo com OP.")
        
        conn.commit()
        
        return jsonify({
            "status": "success", 
            "message": f"Registrado {pulsos} pulsos para máquina {id_maquina}",
            "timestamp": timestamp.isoformat()
        })
        
    except Exception as e:
        logger.error(f"Erro ao registrar pulso: {str(e)}", exc_info=True)
        return jsonify({"status": "error", "message": str(e)}), 500

# Nova rota para registrar dispositivos ESP32
@app.route('/registrar_dispositivo', methods=['POST'])
def registrar_dispositivo():
    try:
        data = request.get_json()
        logger.info(f"Dados recebidos em /registrar_dispositivo: {data}")
        
        # Extrair dados do JSON
        codigo = data.get('codigo') # Este seria o deviceId do ESP32
        id_maquina = data.get('id_maquina')
        ip = data.get('ip') # Este seria o WiFi.localIP() do ESP32
        
        # Validação básica
        if not codigo or not id_maquina:
            return jsonify({"status": "error", "message": "Código do dispositivo e ID da máquina são obrigatórios"}), 400
            
        # Obter timestamp atual
        timestamp = datetime.now()
        
        # Verificar se a máquina existe
        cursor.execute("SELECT IDMaquina FROM TBL_Recurso WHERE IDMaquina = ?", id_maquina)
        maquina = cursor.fetchone()
        
        if not maquina:
            return jsonify({"status": "error", "message": f"Máquina com ID {id_maquina} não encontrada"}), 404
        
        # Verificar se o dispositivo já existe
        cursor.execute("SELECT IDDispositivo FROM PLN_PRD.dbo.TBL_DispositivoESP32 WHERE CodigoDispositivo = ?", codigo)
        dispositivo = cursor.fetchone()
        
        if dispositivo:
            # Atualizar dispositivo existente
            cursor.execute("""
                UPDATE PLN_PRD.dbo.TBL_DispositivoESP32 
                SET IDMaquina = ?, EnderecoIP = ?, UltimaConexao = ?, Status = 1 
                WHERE CodigoDispositivo = ?
            """, id_maquina, ip, timestamp, codigo)
            
            logger.info(f"Dispositivo {codigo} atualizado para máquina {id_maquina}")
        else:
            # Inserir novo dispositivo
            cursor.execute("""
                INSERT INTO PLN_PRD.dbo.TBL_DispositivoESP32 
                (CodigoDispositivo, IDMaquina, EnderecoIP, UltimaConexao, Status) 
                VALUES (?, ?, ?, ?, 1)
            """, codigo, id_maquina, ip, timestamp)
            
            logger.info(f"Novo dispositivo {codigo} registrado para máquina {id_maquina}")
        
        conn.commit()
        
        return jsonify({
            "status": "success", 
            "message": f"Dispositivo {codigo} registrado para máquina {id_maquina}",
            "timestamp": timestamp.isoformat()
        })
        
    except Exception as e:
        logger.error(f"Erro ao registrar dispositivo: {str(e)}", exc_info=True)
        return jsonify({"status": "error", "message": str(e)}), 500

# --- FIM DAS ROTAS NOVAS/MODIFICADAS PARA INTEGRAÇÃO COM ESP32 ---

# Rotas existentes no seu arquivo (cadastro_ordem, consulta_ordens, buscar_produto, dashboard, etc.)
@app.route('/iniciar_execucao', methods=['POST'])
def iniciar_execucao():
    id_ordem = request.form['id_ordem']
    id_maquina = request.form['id_maquina']
    id_operador = request.form['id_operador']

    id_turno = identificar_turno()

    cursor.execute("""
        INSERT INTO TBL_ExecucaoOP (IDOrdem, IDMaquina, IDOperador, IDTurno, DataHoraInicio, Status)
        VALUES (?, ?, ?, ?, GETDATE(), 'Em Execucao')
    """, id_ordem, id_maquina, id_operador, id_turno)
    conn.commit()
    return redirect(url_for('dashboard'))

@app.route('/inserir_op', methods=['POST'])
def inserir_op():
    id_maquina = request.form['id_maquina']
    id_ordem = request.form['id_ordem']
    acao = request.form['acao']  # 'executar' ou 'fila'

    if acao == 'executar':
        cursor.execute("""
            INSERT INTO TBL_FilaOrdem (IDMaquina, IDOrdem, StatusFila)
            VALUES (?, ?, 'executando')
        """, (id_maquina, id_ordem))

        # Executar também na ExecucoesOP (operador fixo = 1)
        id_operador = 1
        id_turno = identificar_turno()

        cursor.execute("""
            INSERT INTO TBL_ExecucaoOP (IDOrdem, IDMaquina, IDOperador, IDTurno, DataHoraInicio, Status)
            VALUES (?, ?, ?, ?, GETDATE(), 'Em Execucao')
        """, id_ordem, id_maquina, id_operador, id_turno)

    elif acao == 'fila':
            cursor.execute(
                "SELECT COUNT(*) FROM TBL_FilaOrdem WHERE IDMaquina = ? AND IDOrdem = ? AND StatusFila IN ('executando', 'pendente')",
                (id_maquina, id_ordem)
            )
            existe = cursor.fetchone()[0]
            if existe > 0:
                cursor.execute("SELECT CodigoInterno, NomeMaquina FROM TBL_Recurso WHERE IDMaquina = ?", (id_maquina,))
                maquina = cursor.fetchone()
                cursor.execute("SELECT IDOrdem, CodigoOrdem FROM TBL_OrdemProducao WHERE IDStatus IN (1, 2, 3)")
                ordens_disponiveis = cursor.fetchall()
                return render_template('adicionar_op.html',
                                       id_maquina=id_maquina,
                                       nome_maquina=maquina.NomeMaquina,
                                       ordens_disponiveis=ordens_disponiveis,
                                       mensagem='Essa OP já está na fila de ordens. Verifique.')
            else:
                cursor.execute(
                    "INSERT INTO TBL_FilaOrdem (IDMaquina, IDOrdem, StatusFila) VALUES (?, ?, 'pendente')",
                    (id_maquina, id_ordem)
                )
                conn.commit()
                cursor.execute("SELECT CodigoInterno, NomeMaquina FROM TBL_Recurso WHERE IDMaquina = ?", (id_maquina,))
                maquina = cursor.fetchone()
                cursor.execute("SELECT IDOrdem, CodigoOrdem FROM TBL_OrdemProducao WHERE IDStatus IN (1, 2, 3)")
                ordens_disponiveis = cursor.fetchall()
                return render_template('adicionar_op.html',
                                       id_maquina=id_maquina,
                                       nome_maquina=maquina.NomeMaquina,
                                       ordens_disponiveis=ordens_disponiveis,
                                       mensagem='OP adicionada com sucesso à fila.')
    return jsonify({'status': 'ok'})

@app.route('/cadastro_ordem', methods=['GET', 'POST'])
@permissao_requerida('/cadastro_ordem')
def cadastro_ordem():
    if request.method == 'POST':
        codigo = request.form['codigo']
        id_produto = request.form['produto']
        quantidade = request.form['quantidade']
        data_inicio = request.form['data_inicio']
        data_fim = request.form['data_fim']
        id_status = 2  # Liberada

        # Buscar dados do produto
        cursor.execute("""
            SELECT CodigoProduto, NomeProduto 
            FROM TBL_Produto 
            WHERE IDProduto = ?
        """, id_produto)
        produto = cursor.fetchone()
        codigo_produto = produto.CodigoProduto
        nome_produto = produto.NomeProduto

        # Buscar nome do status
        cursor.execute("""
            SELECT NomeStatus 
            FROM TBL_StatusOrdemProducao 
            WHERE IDStatus = ?
        """, id_status)
        status = cursor.fetchone()
        nome_status = status.NomeStatus if status else 'Desconhecido'

        # Inserir ordem com todos os dados
        cursor.execute("""
            INSERT INTO TBL_OrdemProducao (
                CodigoOrdem, IDProduto, QuantidadePlanejada, 
                DataInicioPlanejada, DataFimPlanejada, 
                IDStatus, CodigoProduto, NomeProduto, NomeStatus
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, codigo, id_produto, quantidade, data_inicio, data_fim,
             id_status, codigo_produto, nome_produto, nome_status)

        conn.commit()
        return redirect(url_for('cadastro_ordem'))

    # Carrega apenas produtos habilitados
    cursor.execute("SELECT IDProduto, CodigoProduto, NomeProduto FROM TBL_Produto WHERE Habilitado = 1")
    produtos = cursor.fetchall()

    # Consulta ordens com JOIN em status
    cursor.execute("""
        SELECT O.IDOrdem, O.CodigoOrdem, P.NomeProduto, O.QuantidadePlanejada,
               O.DataInicioPlanejada, O.DataFimPlanejada, S.NomeStatus
        FROM TBL_OrdemProducao O
        INNER JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
        INNER JOIN TBL_StatusOrdemProducao S ON O.IDStatus = S.IDStatus
        ORDER BY O.IDOrdem DESC
    """)
    columns = [col[0] for col in cursor.description]
    ordens = [dict(zip(columns, row)) for row in cursor.fetchall()]

    return render_template('cadastro_ordem.html', produtos=produtos, ordens=ordens)

@app.route('/consulta_ordens', methods=['GET', 'POST'])
@permissao_requerida('/consulta_ordens')
def consulta_ordens():
    if request.method == 'POST':
        id_ordem = request.form['id_ordem']
        codigo = request.form['codigo']
        produto = request.form['produto']
        quantidade = request.form['quantidade']
        data_inicio = request.form['data_inicio']
        data_fim = request.form['data_fim']

        cursor.execute("""
            UPDATE TBL_OrdemProducao
            SET CodigoOrdem = ?, IDProduto = ?, QuantidadePlanejada = ?, DataInicioPlanejada = ?, DataFimPlanejada = ?
            WHERE IDOrdem = ?
        """, codigo, produto, quantidade, data_inicio, data_fim, id_ordem)
        conn.commit()
        return redirect(url_for('consulta_ordens'))

    cursor.execute("SELECT IDProduto, NomeProduto FROM TBL_Produto")
    produtos = cursor.fetchall()

    cursor.execute("""
        SELECT O.IDOrdem, O.CodigoOrdem, O.IDProduto, P.NomeProduto, O.QuantidadePlanejada,
               O.DataInicioPlanejada, O.DataFimPlanejada,
               (SELECT NomeStatus FROM TBL_StatusOrdemProducao S WHERE S.IDStatus = O.IDStatus) AS NomeStatus
        FROM TBL_OrdemProducao O
        INNER JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
        ORDER BY O.IDOrdem DESC
    """)
    ordens = cursor.fetchall()

    return render_template('consulta_ordens.html', ordens=ordens, produtos=produtos)

@app.route('/buscar_produto')
def buscar_produto():
    codigo = request.args.get('codigo')
    cursor.execute("SELECT IDProduto, NomeProduto FROM TBL_Produto WHERE CodigoProduto = ?", codigo)
    produto = cursor.fetchone()
    if produto:
        return jsonify({"id": produto.IDProduto, "nome": produto.NomeProduto})
    else:
        return jsonify({"erro": "Produto não encontrado"}), 404, 404
        
# Função auxiliar para obter ID do motivo de parada
def get_motivo_parada_id_by_description(description_like):
    cursor.execute("""
        SELECT TOP 1 IDMotivoParada
        FROM TBL_MotivoParada
        WHERE Descricao LIKE ?
    """, description_like)
    row = cursor.fetchone()
    return row.IDMotivoParada if row else None

@app.route('/dashboard')
@login_requerido
def dashboard():
    try:
        # Obter o setor selecionado do parâmetro de consulta
        setor_selecionado = request.args.get('setor', type=int)
        
        # Buscar todos os setores ativos para o filtro
        cursor.execute("""
            SELECT IDSetor, Nome, Codigo 
            FROM TBL_Setor 
            WHERE Ativo = 1 
            ORDER BY Nome
        """)
        setores = cursor.fetchall()
        
        # Construir a consulta base para recursos
        recursos_query = """
        SELECT IDMaquina, NomeMaquina, CodigoInterno, 
               ISNULL(MetaOEE, 90) AS MetaOEE, 
               ISNULL(MetaQualidade, 95) AS MetaQualidade, 
               ISNULL(MetaDisponibilidade, 92) AS MetaDisponibilidade, 
               ISNULL(MetaPerformance, 93) AS MetaPerformance,
               IDSetor
        FROM TBL_Recurso 
        WHERE Ativo = 1
        """
        
        # Adicionar filtro de setor se um setor foi selecionado
        if setor_selecionado:
            recursos_query += " AND IDSetor = ?"
            cursor.execute(recursos_query, (setor_selecionado,))
        else:
            cursor.execute(recursos_query)

        maquinas = cursor.fetchall()
        recursos = []

        # Verificar e finalizar paradas antigas para todas as máquinas
        for maquina in maquinas:
            finalizar_paradas_antigas(maquina.IDMaquina)

        for maquina in maquinas:
            id_maquina = maquina.IDMaquina
            nome_maquina = maquina.NomeMaquina
            codigo_interno = maquina.CodigoInterno

            # --- INÍCIO DA RECONCILIAÇÃO DE STATUS DA MÁQUINA COM ORDEM DE PRODUÇÃO ---
            # 1. Obter o status atual da máquina na TBL_StatusMaquina
            cursor.execute("""
                SELECT TOP 1 IDStatus, Status, DataHoraInicio, IDMotivoParada
                FROM TBL_StatusMaquina
                WHERE IDMaquina = ?
                ORDER BY DataHoraRegistro DESC
            """, id_maquina)
            current_status_entry = cursor.fetchone()
            
            current_db_status = current_status_entry.Status if current_status_entry else None
            current_db_idstatus = current_status_entry.IDStatus if current_status_entry else None

            # 2. Verificar se há uma Ordem de Produção ativa para esta máquina
            cursor.execute("""
                SELECT TOP 1 IDExecucao
                FROM TBL_ExecucaoOP
                WHERE IDMaquina = ? AND DataHoraFim IS NULL AND Status = 'Em Execucao'
            """, id_maquina)
            active_op_exists = cursor.fetchone() is not None

            # Obter ID do motivo "Aguardando Ordem" ou "Sem OP"
            id_motivo_aguardando_op = get_motivo_parada_id_by_description('%Sem OP%') or \
                                      get_motivo_parada_id_by_description('%Aguardando Ordem%')
            
            # Lógica de reconciliação
            if active_op_exists: # Há uma OP ativa
                if current_db_status == 0: # Máquina está marcada como parada, mas deveria estar rodando
                    logger.info(f"Reconciliação: Máquina {nome_maquina} (ID: {id_maquina}) marcada como parada, mas tem OP ativa. Atualizando para 'Em Execução'.")
                    # Fechar o status atual de parada
                    if current_db_idstatus:
                        cursor.execute("""
                            UPDATE TBL_StatusMaquina
                            SET DataHoraFim = GETDATE(), DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, GETDATE())
                            WHERE IDStatus = ?
                        """, current_db_idstatus)
                    # Inserir novo status de execução
                    cursor.execute("""
                        INSERT INTO TBL_StatusMaquina
                        (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, DescricaoStatus)
                        VALUES (?, 1, GETDATE(), GETDATE(), ?, 'Em Execução')
                    """, (id_maquina, identificar_turno())) # Use identificar_turno() para o turno atual
                    conn.commit()
                elif current_db_status is None: # Sem status registrado, mas tem OP ativa
                    logger.info(f"Reconciliação: Máquina {nome_maquina} (ID: {id_maquina}) sem status, mas tem OP ativa. Inserindo 'Em Execução'.")
                    cursor.execute("""
                        INSERT INTO TBL_StatusMaquina
                        (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, DescricaoStatus)
                        VALUES (?, 1, GETDATE(), GETDATE(), ?, 'Em Execução')
                    """, (id_maquina, identificar_turno()))
                    conn.commit()
                # else: current_db_status == 1, que é consistente. Não faz nada.
            else: # NÃO há OP ativa
                if current_db_status == 1: # Máquina está marcada como rodando, mas não tem OP ativa
                    logger.info(f"Reconciliação: Máquina {nome_maquina} (ID: {id_maquina}) marcada como rodando, mas sem OP ativa. Atualizando para 'Aguardando Ordem'.")
                    # Fechar o status atual de execução
                    if current_db_idstatus:
                        cursor.execute("""
                            UPDATE TBL_StatusMaquina
                            SET DataHoraFim = GETDATE(), DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, GETDATE())
                            WHERE IDStatus = ?
                        """, current_db_idstatus)
                    # Inserir novo status de parada por aguardando ordem
                    cursor.execute("""
                        INSERT INTO TBL_StatusMaquina
                        (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, IDMotivoParada, DescricaoStatus)
                        VALUES (?, 0, GETDATE(), GETDATE(), ?, ?, 'Aguardando Ordem')
                    """, (id_maquina, identificar_turno(), id_motivo_aguardando_op))
                    conn.commit()
                elif current_db_status is None: # Sem status registrado e sem OP ativa
                    logger.info(f"Reconciliação: Máquina {nome_maquina} (ID: {id_maquina}) sem status e sem OP ativa. Inserindo 'Aguardando Ordem'.")
                    cursor.execute("""
                        INSERT INTO TBL_StatusMaquina
                        (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, IDMotivoParada, DescricaoStatus)
                        VALUES (?, 0, GETDATE(), GETDATE(), ?, ?, 'Aguardando Ordem')
                    """, (id_maquina, identificar_turno(), id_motivo_aguardando_op))
                    conn.commit()
                # else: current_db_status == 0, que é consistente. Não faz nada.
            # --- FIM DA RECONCILIAÇÃO ---

            # Verificar estado atual da máquina (após reconciliação)
            estado_maquina = verificar_estado_maquina(id_maquina)
            logger.info(f"Máquina {nome_maquina} está {estado_maquina['estado']}")

            id_turno_atual = identificar_turno()
            logger.info(f"ID do turno atual identificado: {id_turno_atual}")
            
            # Obter disponibilidade com logs detalhados
            disponibilidade_dict = obter_disponibilidade_turno_detalhado(id_maquina, id_turno_atual if id_turno_atual else 1)
            logger.info(f"Disponibilidade retornada: {disponibilidade_dict}")

            tempo_rodando = disponibilidade_dict['TempoRodando']
            tempo_parado = disponibilidade_dict['TempoParado']
            disponibilidade_pct = float(disponibilidade_dict['Disponibilidade_Pct'])

            # Dados da ordem ativa
            cursor.execute("""
                SELECT TOP 1 E.IDOrdem, O.CodigoOrdem, O.QuantidadePlanejada, 
                             O.DataInicioPlanejada, O.DataFimPlanejada,
                             P.CodigoProduto, P.NomeProduto, P.UnidadesporCaixa,
                             P.TempoCicloSegundos
                FROM TBL_ExecucaoOP E
                JOIN TBL_OrdemProducao O ON O.IDOrdem = E.IDOrdem
                JOIN TBL_Produto P ON P.IDProduto = O.IDProduto
                WHERE E.IDMaquina = ?
                AND E.DataHoraFim IS NULL
                AND E.Status = 'Em Execucao'
                ORDER BY E.IDExecucao DESC
            """, id_maquina)

            row_ordem = cursor.fetchone()

            if row_ordem:
                id_ordem = row_ordem.IDOrdem
                codigo_ordem = row_ordem.CodigoOrdem
                quantidade_planejada = row_ordem.QuantidadePlanejada or 0
                data_inicio = row_ordem.DataInicioPlanejada
                data_fim = row_ordem.DataFimPlanejada
                codigo_produto = row_ordem.CodigoProduto
                nome_produto = row_ordem.NomeProduto
                unidades_por_caixa = row_ordem.UnidadesporCaixa or 0
            else:
                id_ordem = None
                codigo_ordem = None
                quantidade_planejada = None
                data_inicio = None
                data_fim = None
                codigo_produto = None
                nome_produto = None
                unidades_por_caixa = 0

            # Qualidade + dados do produto para performance
            quantidade_produzida = 0
            quantidade_refugada = 0
            tempo_ciclo = 0.0
            fator = 1.0
            sigla_unidade = 'UN'

            if id_turno_atual:
                cursor.execute("""
                    SELECT 
                        SUM(CASE WHEN E.TipoValor = 'BOA' THEN E.Quantidade ELSE 0 END) AS TotalBoa,
                        SUM(CASE WHEN E.TipoValor = 'REFUGO' THEN E.Quantidade ELSE 0 END) AS TotalRefugo,
                        P.TempoCicloSegundos,
                        P.FatorMultiplicacao,
                        U.Sigla
                    FROM TBL_EventoProducao E
                    JOIN TBL_OrdemProducao O ON E.IDOrdemProducao = O.IDOrdem
                    JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
                    JOIN TBL_UnidadeMedida U ON P.IDUnidade = U.IDUnidade
                    WHERE 
                        E.IDMaquina = ? 
                        AND E.IDTurno = ? 
                        AND O.IDProduto IS NOT NULL
                    GROUP BY P.TempoCicloSegundos, P.FatorMultiplicacao, U.Sigla
                """, (id_maquina, id_turno_atual))

                row_qualidade = cursor.fetchone()
                if row_qualidade:
                    quantidade_produzida = float(row_qualidade.TotalBoa or 0)
                    quantidade_refugada = float(row_qualidade.TotalRefugo or 0)
                    tempo_ciclo = float(row_qualidade.TempoCicloSegundos or 0)
                    fator = float(row_qualidade.FatorMultiplicacao or 1)
                    sigla_unidade = row_qualidade.Sigla.upper()

            total = quantidade_produzida + quantidade_refugada
            qualidade = round((quantidade_produzida / total) * 100, 1) if total > 0 else 0.0

            caixas_produzidas = 0
            if unidades_por_caixa and unidades_por_caixa > 0:
                caixas_produzidas = quantidade_produzida // unidades_por_caixa

            # Performance baseada no turno
            velocidade_planejada = 0.0
            velocidade_real = 0.0
            performance = 0.0

            if tempo_ciclo > 0:
                tempo_ciclo_unitario = tempo_ciclo / fator if fator > 0 else tempo_ciclo

                # Inicializar variáveis com valores padrão
                velocidade_real = 0.0
                velocidade_planejada = 0.0
                performance = 0.0
    
                try:
                    cursor.execute("SELECT HoraInicio FROM TBL_Turno WHERE IDTurno = ?", (id_turno_atual,))
                    turno_info = cursor.fetchone()
                    if turno_info:
                        # Tratar o campo HoraInicio como objeto time
                        if isinstance(turno_info.HoraInicio, str):
                            hora_inicio_turno = datetime.strptime(turno_info.HoraInicio, '%H:%M').time()
                        else:
                            hora_inicio_turno = turno_info.HoraInicio
                
                        agora = datetime.now()
                        inicio_turno = datetime.combine(agora.date(), hora_inicio_turno)
                        if agora.time() < hora_inicio_turno:
                            inicio_turno -= timedelta(days=1)

                        minutos_decorridos = (agora - inicio_turno).total_seconds() / 60
                        if minutos_decorridos <= 0:
                            minutos_decorridos = 1.0

                        velocidade_real = round(quantidade_produzida / minutos_decorridos, 2)
                        velocidade_planejada = round(60 / tempo_ciclo_unitario, 2)
                        performance = round((velocidade_real / velocidade_planejada) * 100, 1)
                except Exception as e:
                    logger.error(f"Erro ao calcular performance: {e}")
                    velocidade_planejada = round(60 / tempo_ciclo_unitario, 2) if tempo_ciclo_unitario > 0 else 0.0

                    logger.debug("=== DEBUG PERFORMANCE POR TURNO ===")
                    logger.debug(f"ID Máquina: {id_maquina}")
                    logger.debug(f"Turno Atual: {id_turno_atual}")
                    logger.debug(f"Tempo Ciclo (s): {tempo_ciclo}")
                    logger.debug(f"Fator: {fator}")
                    logger.debug(f"Unidade: {sigla_unidade}")
                    logger.debug(f"Velocidade Real (u/min): {velocidade_real}")
                    logger.debug(f"Velocidade Planejada (u/min): {velocidade_planejada}")
                    logger.debug(f"Performance Calculada: {performance}")

                                
            # --- Buscar status máquina (após reconciliação)
            cursor.execute("""
                SELECT TOP 1 Status, DataHoraInicio, IDMotivoParada FROM TBL_StatusMaquina 
                WHERE IDMaquina = ? AND DataHoraFim IS NULL 
                ORDER BY DataHoraInicio DESC
            """, id_maquina)
            row_status = cursor.fetchone()
            
            status_atual_maquina = row_status.Status if row_status else 0
            data_hora_inicio_status = row_status.DataHoraInicio if row_status else None
            id_motivo_parada = row_status.IDMotivoParada if row_status else None
            
            if id_motivo_parada:
                cursor.execute("SELECT Descricao FROM TBL_MotivoParada WHERE IDMotivoParada = ?", id_motivo_parada)
                row_desc = cursor.fetchone()
                descricao_motivo = row_desc.Descricao if row_desc else "Parada Desconhecida"
            else:
                descricao_motivo = None

            
            # --- Nome do turno atual
            if id_turno_atual:
                cursor.execute("SELECT NomeTurno FROM TBL_Turno WHERE IDTurno = ?", id_turno_atual)
                row_turno = cursor.fetchone()
                turno_atual = row_turno.NomeTurno if row_turno else None
            else:
                turno_atual = None  

            # --- Padronizar casas decimais ---
            qualidade = round(float(qualidade), 1)
            performance = round(float(performance), 1)
            disponibilidade_pct = round(float(disponibilidade_pct), 1)    

            # --- Cálculo de OEE ---
            try:
                oee = round((disponibilidade_pct * performance * qualidade) / 10000, 1)
            except Exception as e:
                logger.error(f"Erro ao calcular OEE: {e}")
                oee = 0.0

            # --- Buscar nome do setor ---
            id_setor = maquina.IDSetor
            nome_setor = None
            if id_setor:
                cursor.execute("SELECT Nome FROM TBL_Setor WHERE IDSetor = ?", (id_setor,))
                setor_row = cursor.fetchone()
                nome_setor = setor_row.Nome if setor_row else None

            recurso = {
                'IDMaquina': id_maquina,
                'NomeMaquina': nome_maquina,
                'CodigoInterno': codigo_interno,
                'StatusAtual': status_atual_maquina,
                'OrdemAtual': codigo_ordem,
                'CodigoProduto': codigo_produto,
                'NomeProduto': nome_produto,
                'QuantidadePlanejada': quantidade_planejada,
                'QuantidadeProduzida': quantidade_produzida,
                'QuantidadeRefugada': quantidade_refugada,
                'DataInicio': data_inicio,
                'DataFim': data_fim,
                'TurnoAtual': turno_atual,
                'Qualidade': qualidade,
                'Disponibilidade': disponibilidade_pct,
                'Performance': performance,
                'OEE': oee,
                'CaixasProduzidas': caixas_produzidas,
                'VelocidadePlanejada': velocidade_planejada,
                'VelocidadeReal': velocidade_real,
                'MetaOEE': maquina.MetaOEE,
                'MetaQualidade': maquina.MetaQualidade,
                'MetaDisponibilidade': maquina.MetaDisponibilidade,
                'MetaPerformance': maquina.MetaPerformance,
                'TempoRodando': tempo_rodando,
                'TempoParado': tempo_parado,
                'Disponibilidade_Pct': disponibilidade_pct,
                "DataHoraInicioStatus": data_hora_inicio_status,
                'IDMotivoParada': id_motivo_parada,
                'DescricaoMotivoParada': descricao_motivo,
                'IDSetor': id_setor,
                'NomeSetor': nome_setor,
                'EstadoMaquina': estado_maquina['estado']
            }
            
            logger.info(f"Máquina {nome_maquina} | Ordem: {codigo_ordem} | Produzido: {quantidade_produzida} unidades | Tempo Ciclo: {tempo_ciclo} seg | Performance: {performance}% | Vel Planejada: {velocidade_planejada} u/min | Vel Real: {velocidade_real} u/min | Disponibilidade: {disponibilidade_pct}%")

            recursos.append(recurso)

        # --- operador e motivos de refugo
        cursor.execute("SELECT IDOperador, NomeOperador FROM TBL_Operador WHERE Ativo = 1")
        operador = cursor.fetchall()

        cursor.execute("SELECT IDMotivoRefugo, Descricao FROM TBL_MotivoRefugo")
        motivos_refugo = cursor.fetchall()
        
        # --- Motivos de parada
        cursor.execute("SELECT IDMotivoParada, Descricao FROM TBL_MotivoParada WHERE Sistema = 0")
        motivos_parada = [dict(zip([col[0] for col in cursor.description], row)) for row in cursor.fetchall()]
        
        # --- ID do motivo padrão do sistema (ex: 'Parada Não Identificada')
        cursor.execute("SELECT TOP 1 IDMotivoParada FROM TBL_MotivoParada WHERE Sistema = 1")
        row = cursor.fetchone()
        id_motivo_padrao = row[0] if row else None

        for recurso in recursos:
            recurso['StatusAtual'] = int(recurso['StatusAtual']) if recurso['StatusAtual'] is not None else 0
        
        return render_template(
            'dashboard.html',
            recursos=recursos,
            operador=operador,
            motivos_refugo=motivos_refugo,
            motivos_parada=motivos_parada,
            id_motivo_padrao=id_motivo_padrao,
            setores=setores,
            setor_selecionado=setor_selecionado
        )
    except Exception as e:
        logger.error(f"Erro no dashboard: {e}")
        import traceback
        logger.error(traceback.format_exc())
        return render_template('erro.html', mensagem=f"Erro ao carregar o dashboard: {str(e)}")

@app.route('/')
def index():
    return redirect(url_for('cadastro_produto'))

@app.route('/adicionar_op/<int:id_maquina>', methods=['GET', 'POST'])
# A rota abaixo estava duplicada no seu arquivo original. Removida para evitar conflitos.
# @app.route("/fila_ordens/<int:id_maquina>") 
def adicionar_op(id_maquina):
    if request.method == 'POST':
        id_ordem = request.form['id_ordem']
        acao = request.form['acao']

        if acao == 'executar':
            # Adiciona na fila com status executando
            cursor.execute("""
                INSERT INTO TBL_FilaOrdem (IDMaquina, IDOrdem, StatusFila)
                VALUES (?, ?, 'executando')
            """, (id_maquina, id_ordem))

            # Define operador fixo
            id_operador = 1

            # Carrega os turnos ativos (faltava isso antes!)
            cursor.execute("SELECT IDTurno, HoraInicio, HoraFim FROM TBL_Turno WHERE Ativo = 1")
            turnos = cursor.fetchall()

            if not turnos:
                return "Nenhum turno ativo cadastrado. Não é possível iniciar a OP.", 400

            # Pega hora atual
            agora = datetime.now().time()
            hora_atual = agora

            id_turno = None

            # Identifica o turno atual
            for turno in turnos:
                inicio = turno.HoraInicio
                fim = turno.HoraFim

                if inicio < fim:
                    if inicio <= hora_atual <= fim:
                        id_turno = turno.IDTurno
                        break
                else:
                    # Turnos que passam da meia-noite
                    if hora_atual >= inicio or hora_atual <= fim:
                        id_turno = turno.IDTurno
                        break

            if id_turno is None:
                return "Nenhum turno correspondente encontrado para o horário atual.", 400

            # Registra na ExecucoesOP
            cursor.execute("""
                INSERT INTO TBL_ExecucaoOP (IDOrdem, IDMaquina, IDOperador, IDTurno, DataHoraInicio, Status)
                VALUES (?, ?, ?, ?, GETDATE(), 'Em Execucao')
            """, id_ordem, id_maquina, id_operador, id_turno)

            conn.commit()

        elif acao == 'fila':
            # Verifica se já está na fila
            cursor.execute(
                "SELECT COUNT(*) FROM TBL_FilaOrdem WHERE IDMaquina = ? AND IDOrdem = ? AND StatusFila IN ('executando', 'pendente')",
                (id_maquina, id_ordem)
            )
            existe = cursor.fetchone()[0]

            if existe > 0:
                cursor.execute("SELECT CodigoInterno, NomeMaquina FROM TBL_Recurso WHERE IDMaquina = ?", (id_maquina,))
                maquina = cursor.fetchone()

                cursor.execute("SELECT IDOrdem, CodigoOrdem FROM TBL_OrdemProducao WHERE IDStatus IN (1, 2, 3)")
                ordens_disponiveis = cursor.fetchall()

                return render_template('adicionar_op.html',
                                       id_maquina=id_maquina,
                                       nome_maquina=maquina.NomeMaquina,
                                       ordens_disponiveis=ordens_disponiveis,
                                       mensagem='Essa OP já está na fila de ordens. Verifique.')
            else:
                cursor.execute(
                    "INSERT INTO TBL_FilaOrdem (IDMaquina, IDOrdem, StatusFila) VALUES (?, ?, 'pendente')",
                    (id_maquina, id_ordem)
                )
                conn.commit()

                cursor.execute("SELECT CodigoInterno, NomeMaquina FROM TBL_Recurso WHERE IDMaquina = ?", (id_maquina,))
                maquina = cursor.fetchone()

                cursor.execute("SELECT IDOrdem, CodigoOrdem FROM TBL_OrdemProducao WHERE IDStatus IN (1, 2, 3)")
                ordens_disponiveis = cursor.fetchall()

                return render_template('adicionar_op.html',
                                       id_maquina=id_maquina,
                                       nome_maquina=maquina.NomeMaquina,
                                       ordens_disponiveis=ordens_disponiveis,
                                       mensagem='OP adicionada com sucesso à fila.')

        return redirect(url_for('dashboard'))

    # Se for GET, renderiza o formulário com as ordens disponíveis
    cursor.execute("SELECT CodigoInterno, NomeMaquina FROM TBL_Recurso WHERE IDMaquina = ?", (id_maquina,))
    maquina = cursor.fetchone()

    cursor.execute("SELECT IDOrdem, CodigoOrdem FROM TBL_OrdemProducao WHERE IDStatus IN (1, 2, 3)")
    ordens_disponiveis = cursor.fetchall()

    return render_template('adicionar_op.html',
                           id_maquina=id_maquina,
                           nome_maquina=maquina.NomeMaquina,
                           ordens_disponiveis=ordens_disponiveis)

@app.route('/interromper_op', methods=['POST'])
def interromper_op():
    try:
        data = request.get_json()
        id_maquina = data.get('id_maquina')
        
        if not id_maquina:
            return jsonify({'success': False, 'message': 'ID da máquina não fornecido'})
        
        # Buscar a execução de OP ativa
        cursor.execute("""
            SELECT TOP 1 IDExecucao, IDOrdem
            FROM TBL_ExecucaoOP
            WHERE IDMaquina = ?
            AND DataHoraFim IS NULL
            AND Status = 'Em Execucao'
            ORDER BY DataHoraInicio DESC
        """, id_maquina)
        
        row = cursor.fetchone()
        if not row:
            return jsonify({'success': False, 'message': 'Nenhuma OP em execução para esta máquina'})
        
        id_execucao = row.IDExecucao
        id_ordem = row.IDOrdem
        
        # Atualizar o status da execução para "Interrompida"
        cursor.execute("""
            UPDATE TBL_ExecucaoOP
            SET Status = 'Interrompida', DataHoraFim = GETDATE()
            WHERE IDExecucao = ?
        """, id_execucao)
        
        # Atualizar o status da máquina para "Parada"
        # Primeiro, verificar se já existe um status ativo
        cursor.execute("""
            SELECT TOP 1 IDStatus
            FROM TBL_StatusMaquina
            WHERE IDMaquina = ?
            AND DataHoraFim IS NULL
            ORDER BY DataHoraInicio DESC
        """, id_maquina)
        
        row_status = cursor.fetchone()
        if row_status:
            # Finalizar o status atual
            cursor.execute("""
                UPDATE TBL_StatusMaquina
                SET DataHoraFim = GETDATE()
                WHERE IDStatus = ?
            """, row_status.IDStatus)
        
        # Buscar o ID do motivo de parada padrão (por exemplo, "Interrupção de OP")
        cursor.execute("""
            SELECT TOP 1 IDMotivoParada
            FROM TBL_MotivoParada
            WHERE Descricao LIKE '%Interrup%'
            OR Descricao LIKE '%Parada Operacional%'
        """)
        
        row_motivo = cursor.fetchone()
        id_motivo_parada = row_motivo.IDMotivoParada if row_motivo else None
        
        # Inserir novo status "Parado"
        cursor.execute("""
            INSERT INTO TBL_StatusMaquina (
                IDMaquina, Status, DataHoraInicio, IDMotivoParada, ObsEvento
            ) VALUES (?, 0, GETDATE(), ?, 'OP interrompida pelo usuário')
        """, (id_maquina, id_motivo_parada))
        
        conn.commit()
        
        return jsonify({'success': True})
    
    except Exception as e:
        conn.rollback()
        logger.error(f"Erro ao interromper OP: {e}")
        return jsonify({'success': False, 'message': str(e)})
        
def finalizar_paradas_antigas(id_maquina):
    """
    Finaliza paradas antigas que possam ter ficado abertas por erro.
    """
    try:
        # Encontrar status sem fim registrado mais antigos que 8 horas
        limite_tempo = datetime.now() - timedelta(hours=8)
        
        cursor.execute("""
            SELECT IDStatus
            FROM TBL_StatusMaquina
            WHERE IDMaquina = ? AND DataHoraFim IS NULL AND DataHoraInicio < ?
        """, (id_maquina, limite_tempo))
        
        status_antigos = cursor.fetchall()
        
        if status_antigos:
            logger.warning(f"Encontrados {len(status_antigos)} status antigos não finalizados para máquina {id_maquina}")
            
            for status in status_antigos:
                cursor.execute("""
                    UPDATE TBL_StatusMaquina
                    SET DataHoraFim = ?
                    WHERE IDStatus = ?
                """, (datetime.now(), status.IDStatus))
                
                logger.info(f"Status ID {status.IDStatus} finalizado automaticamente")
            
            conn.commit()
            return True
        
        return False
    
    except Exception as e:
        logger.error(f"Erro ao finalizar paradas antigas: {e}")
        return False

def verificar_estado_maquina(id_maquina):
    """
    Verifica se a máquina está em operação ou parada.
    Retorna um dicionário com o estado e o tempo no estado atual.
    """
    try:
        # Verificar se existe um status de parada não finalizado
        cursor.execute("""
            SELECT TOP 1 DataHoraInicio, Status
            FROM TBL_StatusMaquina
            WHERE IDMaquina = ? AND DataHoraFim IS NULL
            ORDER BY DataHoraInicio DESC
        """, id_maquina)
        
        status_atual = cursor.fetchone()
        
        if status_atual:
            if status_atual.Status == 0:  # Assumindo que 0 = parada
                # Máquina está parada
                tempo_no_estado = (datetime.now() - status_atual.DataHoraInicio).total_seconds()
                return {
                    'estado': 'parada',
                    'tempo_no_estado': tempo_no_estado,
                    'inicio_estado': status_atual.DataHoraInicio
                }
            else:  # Status = 1 (operando)
                tempo_no_estado = (datetime.now() - status_atual.DataHoraInicio).total_seconds()
                return {
                    'estado': 'operando',
                    'tempo_no_estado': tempo_no_estado,
                    'inicio_estado': status_atual.DataHoraInicio
                }
        
        # Se não tiver status atual, considerar como desconhecido
        return {
            'estado': 'desconhecido',
            'tempo_no_estado': 0,
            'inicio_estado': None
        }
    
    except Exception as e:
        logger.error(f"Erro ao verificar estado da máquina {id_maquina}: {e}")
        return {
            'estado': 'erro',
            'tempo_no_estado': 0,
            'inicio_estado': None
        }

def obter_disponibilidade_turno_detalhado(id_maquina, id_turno=1):
    """
    Calcula a disponibilidade de uma máquina para um turno específico com logs detalhados.
    Retorna um dicionário com os tempos e a porcentagem de disponibilidade.
    """
    try:
        logger.info(f"Calculando disponibilidade para máquina {id_maquina} no turno {id_turno}")
        
        # Obter informações do turno
        cursor.execute("""
            SELECT HoraInicio, HoraFim
            FROM TBL_Turno
            WHERE IDTurno = ?
        """, id_turno)

        turno = cursor.fetchone()
        if not turno:
            logger.warning(f"Turno ID {id_turno} não encontrado no banco de dados")
            return {
                'TempoRodando': 0,
                'TempoParado': 0,
                'Disponibilidade_Pct': 0.0
            }

        logger.info(f"Turno encontrado: Início {turno.HoraInicio}, Fim {turno.HoraFim}")
        
        # Obter hora atual
        agora = datetime.now()
        logger.info(f"Hora atual: {agora}")
        
        # Obter hora e minuto diretamente do objeto time
        hora_inicio = turno.HoraInicio.hour
        minuto_inicio = turno.HoraInicio.minute
        
        hora_fim = turno.HoraFim.hour
        minuto_fim = turno.HoraFim.minute
        
        # Criar objetos datetime para o início e fim do turno no dia atual
        inicio_turno = datetime(agora.year, agora.month, agora.day, hora_inicio, minuto_inicio)
        fim_turno = datetime(agora.year, agora.month, agora.day, hora_fim, minuto_fim)
        
        # Se o fim do turno for antes do início, significa que o turno passa para o dia seguinte
        if fim_turno < inicio_turno:
            fim_turno += timedelta(days=1)
            logger.info("Turno passa para o dia seguinte")
            
        # Se a hora atual for antes do início do turno, considerar o turno do dia anterior
        if agora < inicio_turno:
            inicio_turno -= timedelta(days=1)
            fim_turno -= timedelta(days=1)
            logger.info("Considerando turno do dia anterior")
            
        logger.info(f"Período do turno ajustado: {inicio_turno} até {fim_turno}")
        
        # Verificar se estamos dentro do turno
        if agora < inicio_turno or agora > fim_turno:
            logger.warning(f"Fora do horário de turno. Atual: {agora}, Turno: {inicio_turno} - {fim_turno}")
            return {
                'TempoRodando': 0,
                'TempoParado': 0,
                'Disponibilidade_Pct': 0.0
            }
            
        # Calcular o tempo decorrido do turno até agora (em segundos)
        tempo_decorrido = (agora - inicio_turno).total_seconds()
        logger.info(f"Tempo decorrido do turno: {tempo_decorrido/60:.2f} minutos")
        
        # Verificar paradas existentes usando TBL_StatusMaquina
        cursor.execute("""
            SELECT IDStatus, DataHoraInicio, DataHoraFim, IDMotivoParada
            FROM TBL_StatusMaquina
            WHERE IDMaquina = ? AND Status = 0 AND 
                  ((DataHoraInicio >= ? AND DataHoraInicio <= ?) OR
                   (DataHoraFim >= ? AND DataHoraFim <= ?) OR
                   (DataHoraInicio <= ? AND (DataHoraFim >= ? OR DataHoraFim IS NULL)))
            ORDER BY DataHoraInicio DESC
        """, (id_maquina, inicio_turno, agora, inicio_turno, agora, inicio_turno, inicio_turno))
        
        paradas = cursor.fetchall()
        logger.info(f"Encontradas {len(paradas) if paradas else 0} paradas para a máquina no período")
        
        for p in paradas:
            logger.info(f"Status ID: {p.IDStatus}, Início: {p.DataHoraInicio}, Fim: {p.DataHoraFim}, Motivo: {p.IDMotivoParada}")
        
        # Obter os tempos de parada para a máquina no período do turno
        cursor.execute("""
            SELECT 
                SUM(DATEDIFF(SECOND, 
                    CASE 
                        WHEN DataHoraInicio < ? THEN ? 
                        ELSE DataHoraInicio 
                    END, 
                    CASE 
                        WHEN DataHoraFim IS NULL THEN GETDATE() 
                        WHEN DataHoraFim > ? THEN ?
                        ELSE DataHoraFim 
                    END
                )) as TempoParadaTotal
            FROM TBL_StatusMaquina
            WHERE IDMaquina = ? AND Status = 0
              AND (
                  (DataHoraInicio >= ? AND DataHoraInicio <= ?) OR
                  (DataHoraFim >= ? AND DataHoraFim <= ?) OR
                  (DataHoraInicio <= ? AND (DataHoraFim >= ? OR DataHoraFim IS NULL))
              )
        """, (inicio_turno, inicio_turno, agora, agora, id_maquina, 
              inicio_turno, agora, inicio_turno, agora, inicio_turno, inicio_turno))
        
        resultado = cursor.fetchone()
        logger.info(f"Resultado da consulta de tempo parado: {resultado}")
        
        # Tratamento adequado para valores nulos
        if resultado and resultado[0] is not None:
            tempo_parado = float(resultado[0])
        else:
            tempo_parado = 0.0
        
        logger.info(f"Tempo parado calculado: {tempo_parado/60:.2f} minutos")
        
        # Garantir que o tempo parado não exceda o tempo decorrido
        tempo_parado = min(tempo_parado, tempo_decorrido)
        
        # Calcular o tempo rodando (tempo decorrido menos tempo parado)
        tempo_rodando = tempo_decorrido - tempo_parado
        logger.info(f"Tempo rodando calculado: {tempo_rodando/60:.2f} minutos")
        
        # Calcular a disponibilidade como porcentagem
        disponibilidade = (tempo_rodando / tempo_decorrido) * 100 if tempo_decorrido > 0 else 0.0
        logger.info(f"Disponibilidade calculada: {disponibilidade:.2f}%")
        
        # Verificar se a máquina está ativa com base no status atual
        try:
            cursor.execute("""
                SELECT TOP 1 Status
                FROM TBL_StatusMaquina
                WHERE IDMaquina = ?
                ORDER BY DataHoraInicio DESC
            """, id_maquina)
            
            status_atual = cursor.fetchone()
            maquina_ativa = status_atual and status_atual.Status == 1  # Assumindo que 1 = operando
            
            logger.info(f"Status atual da máquina: {maquina_ativa}")
            
            # Se a máquina está ativa mas disponibilidade baixa, ajustar
            if maquina_ativa and disponibilidade < 1.0:
                logger.warning(f"Máquina ativa mas disponibilidade baixa. Ajustando disponibilidade.")
                tempo_rodando = max(tempo_rodando, 60)  # Pelo menos 1 minuto rodando
                tempo_parado = tempo_decorrido - tempo_rodando
                disponibilidade = (tempo_rodando / tempo_decorrido) * 100
                logger.info(f"Disponibilidade ajustada: {disponibilidade:.2f}%")
        except Exception as e:
            logger.error(f"Erro ao verificar status atual: {e}")
        
        return {
            'TempoRodando': round(tempo_rodando),
            'TempoParado': round(tempo_parado),
            'Disponibilidade_Pct': round(disponibilidade, 1)
        }
        
    except Exception as e:
        logger.error(f"Erro ao calcular disponibilidade: {e}")
        import traceback
        logger.error(traceback.format_exc())
        return {
            'TempoRodando': 0,
            'TempoParado': 0,
            'Disponibilidade_Pct': 0.0
        }

@app.route('/finalizar_op', methods=['POST'])
def finalizar_op():
    try:
        data = request.get_json()
        id_maquina = data.get('id_maquina')
        
        if not id_maquina:
            return jsonify({'success': False, 'message': 'ID da máquina não fornecido'})
        
        # Buscar a execução de OP ativa
        cursor.execute("""
            SELECT TOP 1 IDExecucao, IDOrdem
            FROM TBL_ExecucaoOP
            WHERE IDMaquina = ?
            AND DataHoraFim IS NULL
            AND Status = 'Em Execucao'
            ORDER BY DataHoraInicio DESC
        """, id_maquina)
        
        row = cursor.fetchone()
        if not row:
            return jsonify({'success': False, 'message': 'Nenhuma OP em execução para esta máquina'})
        
        id_execucao = row.IDExecucao
        id_ordem = row.IDOrdem
        
        # Atualizar o status da execução para "Finalizada"
        cursor.execute("""
            UPDATE TBL_ExecucaoOP
            SET Status = 'Finalizada', DataHoraFim = GETDATE()
            WHERE IDExecucao = ?
        """, id_execucao)
        
        # Verificar se há mais OPs na fila para esta máquina
        cursor.execute("""
            SELECT TOP 1 IDExecucao
            FROM TBL_ExecucaoOP
            WHERE IDMaquina = ?
            AND Status = 'Aguardando'
            ORDER BY Sequencia ASC
        """, id_maquina)
        
        proxima_op = cursor.fetchone()
        
        if not proxima_op:
            # Se não houver próxima OP, atualizar o status da máquina para "Parada"
            # Primeiro, verificar se já existe um status ativo
            cursor.execute("""
                SELECT TOP 1 IDStatus
                FROM TBL_StatusMaquina
                WHERE IDMaquina = ?
                AND DataHoraFim IS NULL
                ORDER BY DataHoraInicio DESC
            """, id_maquina)
            
            row_status = cursor.fetchone()
            if row_status:
                # Finalizar o status atual
                cursor.execute("""
                    UPDATE TBL_StatusMaquina
                    SET DataHoraFim = GETDATE()
                    WHERE IDStatus = ?
                """, row_status.IDStatus)
            
            # Buscar o ID do motivo de parada padrão (por exemplo, "Sem OP")
            cursor.execute("""
                SELECT TOP 1 IDMotivoParada
                FROM TBL_MotivoParada
                WHERE Descricao LIKE '%Sem OP%'
                OR Descricao LIKE '%Aguardando Ordem%'
            """)
            
            row_motivo = cursor.fetchone()
            id_motivo_parada = row_motivo.IDMotivoParada if row_motivo else None
            
            # Inserir novo status "Parado"
            cursor.execute("""
                INSERT INTO TBL_StatusMaquina (
                    IDMaquina, Status, DataHoraInicio, IDMotivoParada, ObsEvento
                ) VALUES (?, 0, GETDATE(), ?, 'OP finalizada pelo usuário')
            """, (id_maquina, id_motivo_parada))
        
        # Atualizar o status da ordem para "Finalizada" se todas as execuções estiverem concluídas
        cursor.execute("""
            SELECT COUNT(*)
            FROM TBL_ExecucaoOP
            WHERE IDOrdem = ?
            AND DataHoraFim IS NULL
        """, id_ordem)
        
        execucoes_pendentes = cursor.fetchone()[0]
        
        if execucoes_pendentes == 0:
            cursor.execute("""
                UPDATE TBL_OrdemProducao
                SET Status = 'Finalizada', DataHoraFim = GETDATE()
                WHERE IDOrdem = ?
                AND Status <> 'Finalizada'
            """, id_ordem)
        
        conn.commit()
        
        return jsonify({'success': True})
    
    except Exception as e:
        conn.rollback()
        logger.error(f"Erro ao finalizar OP: {e}")
        return jsonify({'success': False, 'message': str(e)})
    
@app.route('/fila_ordens/<int:id_maquina>', methods=['GET', 'POST'])
def fila_ordens(id_maquina):
    cursor.execute("""
        SELECT f.IDOrdem, f.IDMaquina, f.DataInsercao, f.OrdemFila, o.CodigoOrdem,
               p.NomeProduto, o.QuantidadePlanejada
        FROM TBL_FilaOrdem f
        JOIN TBL_OrdemProducao o ON o.IDOrdem = f.IDOrdem
        JOIN TBL_Produto p ON p.IDProduto = o.IDProduto
        WHERE f.IDMaquina = ?
          AND o.IDStatus != 5
        ORDER BY f.OrdemFila
    """, (id_maquina,))
    ordens = cursor.fetchall()
    operador_logado = 1
    turno_atual = 1
    return render_template("fila_ordens.html", ordens=ordens,
                           operador_logado=operador_logado,
                           turno_atual=turno_atual)

@app.route('/remover_fila/<int:id_maquina>/<int:id_ordem>', methods=['POST'])
def remover_fila(id_maquina, id_ordem):
    cursor.execute("DELETE FROM TBL_FilaOrdem WHERE IDMaquina = ? AND IDOrdem = ?", (id_maquina, id_ordem))
    conn.commit()
    return redirect(url_for('fila_ordens', id_maquina=id_maquina))
    
@app.route('/relatorio_producao', methods=['GET', 'POST'])
def relatorio_producao():
    filtros = {
        "data_inicio": request.form.get("data_inicio"),
        "data_fim": request.form.get("data_fim"),
        "id_maquina": request.form.get("id_maquina"),
        "id_produto": request.form.get("id_produto"),
        "codigo_op": request.form.get("codigo_op"),
        "id_operador": request.form.get("id_operador")
    }

    try:
        if filtros["data_inicio"]:
            filtros["data_inicio"] = datetime.strptime(filtros["data_inicio"], "%Y-%m-%d")
        if filtros["data_fim"]:
            filtros["data_fim"] = datetime.strptime(filtros["data_fim"], "%Y-%m-%d").replace(hour=23, minute=59, second=59)
    except:
        filtros["data_inicio"] = None
        filtros["data_fim"] = None

    query = '''
        SELECT 
            R.NomeMaquina,
            O.CodigoOrdem,
            P.CodigoProduto,
            P.NomeProduto,
            ISNULL(SUM(CASE WHEN E.TipoValor = 'BOA' THEN E.Quantidade ELSE 0 END), 0) AS QuantidadeProduzida,
            ISNULL(SUM(CASE WHEN E.TipoValor = 'REFUGO' THEN E.Quantidade ELSE 0 END), 0) AS QuantidadeRefugada,
            O.QuantidadePlanejada,
            T.NomeTurno,
            Op.NomeOperador,
            MIN(E.DataHoraEvento) AS DataHoraInicio,
            MAX(E.DataHoraEvento) AS DataHoraFim
        FROM TBL_EventoProducao E
        INNER JOIN TBL_Recurso R ON E.IDRecurso = R.IDMaquina
        INNER JOIN TBL_OrdemProducao O ON E.IDOrdemProducao = O.IDOrdem
        INNER JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
        LEFT JOIN TBL_Turno T ON E.IDTurno = T.IDTurno
        LEFT JOIN TBL_Operador Op ON E.IDOperador = Op.IDOperador
        WHERE 1=1
          AND E.TipoValor IN ('BOA', 'REFUGO')
    '''
    params = []

    if filtros["data_inicio"]:
        query += " AND E.DataHoraEvento >= ?"
        params.append(filtros["data_inicio"])
    if filtros["data_fim"]:
        query += " AND E.DataHoraEvento <= ?"
        params.append(filtros["data_fim"])
    if filtros["id_maquina"]:
        query += " AND E.IDRecurso = ?"
        params.append(filtros["id_maquina"])
    if filtros["id_produto"]:
        query += " AND O.IDProduto = ?"
        params.append(filtros["id_produto"])
    if filtros["codigo_op"]:
        query += " AND O.CodigoOrdem LIKE ?"
        params.append(f"%{filtros['codigo_op']}%")
    if filtros["id_operador"]:
        query += " AND E.IDOperador = ?"
        params.append(filtros["id_operador"])

    query += '''
        GROUP BY R.NomeMaquina, O.CodigoOrdem, P.CodigoProduto, P.NomeProduto,
                 O.QuantidadePlanejada, T.NomeTurno, Op.NomeOperador
        ORDER BY DataHoraInicio DESC
    '''

    cursor.execute(query, params)
    resultados = cursor.fetchall()

    # Listas para filtros
    cursor.execute("SELECT IDMaquina, NomeMaquina FROM TBL_Recurso WHERE Ativo = 1")
    maquinas = cursor.fetchall()

    cursor.execute("SELECT IDProduto, NomeProduto FROM TBL_Produto")
    produtos = cursor.fetchall()

    cursor.execute("SELECT IDOperador, NomeOperador FROM TBL_Operador WHERE Ativo = 1")
    operador = cursor.fetchall()

    return render_template("relatorio_producao.html", resultados=resultados, filtros=filtros,
                           maquinas=maquinas, produtos=produtos, operador=operador)
        
@app.route('/remover_da_fila', methods=['POST'])
def remover_da_fila():
    id_ordem = request.form.get("id_ordem")
    id_maquina = request.form.get("id_maquina")
    cursor.execute("DELETE FROM TBL_FilaOrdem WHERE IDOrdem = ? AND IDMaquina = ?", (id_ordem, id_maquina))
    conn.commit()
    return redirect(url_for('fila_ordens', id_maquina=id_maquina))

@app.route('/iniciar_op_fila', methods=['POST'])
def iniciar_op_fila():
    id_ordem = request.form.get('id_ordem')
    id_maquina = request.form.get('id_maquina')
    id_turno = request.form.get('id_turno')
    id_operador = request.form.get('id_operador')

    # Remove da fila caso ainda esteja
    cursor.execute("DELETE FROM TBL_FilaOrdem WHERE IDOrdem = ? AND IDMaquina = ?", (id_ordem, id_maquina))

    # Verifica se já está em execução (proteção extra)
    cursor.execute("""
        SELECT COUNT(*) FROM TBL_ExecucaoOP
        WHERE IDOrdem = ? AND IDMaquina = ? AND Status = 'Em Execucao'
    """, (id_ordem, id_maquina))
    existe_execucao = cursor.fetchone()[0]

    if existe_execucao == 0:
        # Atualiza status da ordem para Em Execucao (IDStatus = 5)
        cursor.execute("UPDATE TBL_OrdemProducao SET IDStatus = 5 WHERE IDOrdem = ?", (id_ordem,))

        # Cria nova execução
        cursor.execute("""
            INSERT INTO TBL_ExecucaoOP (IDOrdem, IDMaquina, IDOperador, IDTurno, DataHoraInicio, Status)
            VALUES (?, ?, ?, ?, GETDATE(), 'Em Execucao')
        """, (id_ordem, id_maquina, id_operador, id_turno))

        conn.commit()

    return redirect(url_for('dashboard'))

@app.route("/salvar_ordem_fila", methods=["POST"])
def salvar_ordem_fila():
    ordens = request.form.getlist("ordem_id")
    posicoes = request.form.getlist("ordem_posicao")

    for id_ordem, nova_pos in zip(ordens, posicoes):
        cursor.execute("UPDATE TBL_FilaOrdem SET OrdemFila = ? WHERE IDOrdem = ?", (nova_pos, id_ordem))

    conn.commit()
    return redirect(url_for('fila_ordens', id_maquina=request.form.get('id_maquina')))
    
@app.route('/registrar_parada', methods=['POST'])
def registrar_parada():
    data = request.json
    id_maquina = data['id_maquina']
    id_motivo = int(data['id_motivo'])
    correcao_status = bool(data.get('correcao_status', False))

    # 🔄 Buscar execução ativa para consolidar produção antes da parada
    cursor.execute("""
        SELECT TOP 1 E.IDExecucao, E.IDOrdem, E.IDTurno, R.IDTipo
        FROM TBL_ExecucaoOP E
        JOIN TBL_Recurso R ON R.IDMaquina = E.IDMaquina
        WHERE E.IDMaquina = ? AND E.DataHoraFim IS NULL AND E.Status = 'Em Execucao'
        ORDER BY E.IDExecucao DESC
    """, (id_maquina,))
    execucao = cursor.fetchone()

    if execucao:
        id_execucao, id_ordem, id_turno_exec, id_tipo_recurso = execucao
        id_operador = 1  # ajuste conforme seu sistema real
        chave = (id_execucao, id_maquina, id_tipo_recurso, id_ordem, id_turno_exec, id_operador)
        forcar_gravacao_consolidada(chave)

    # 🔎 Buscar status atual
    cursor.execute("""
        SELECT TOP 1 IDStatus, IDMotivoParada, DataHoraInicio FROM TBL_StatusMaquina 
        WHERE IDMaquina = ? AND DataHoraFim IS NULL
        ORDER BY DataHoraInicio DESC
    """, (id_maquina,))
    row = cursor.fetchone()

    # 🔍 Identificar turno atual
    agora = datetime.now().time()
    cursor.execute("""
        SELECT TOP 1 IDTurno FROM TBL_Turno
        WHERE 
            ((HoraInicio <= ? AND HoraFim > ?) OR
             (HoraInicio > HoraFim AND (HoraInicio <= ? OR HoraFim > ?)))
            AND Ativo = 1
    """, (agora, agora, agora, agora))
    turno = cursor.fetchone()
    id_turno = turno[0] if turno else None

    if row:
        id_status_atual, motivo_atual, data_inicio = row

        if correcao_status:
            cursor.execute("""
                UPDATE TBL_StatusMaquina 
                SET IDMotivoParada = ?, DescricaoStatus = 'Parada'
                WHERE IDStatus = ?
            """, (id_motivo, id_status_atual))

        elif motivo_atual == 11:
            cursor.execute("""
                UPDATE TBL_StatusMaquina 
                SET IDMotivoParada = ?, 
                    DataHoraFim = GETDATE(),
                    DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, GETDATE()),
                    DescricaoStatus = 'Parada'
                WHERE IDStatus = ?
            """, (id_motivo, id_status_atual))

        else:
            cursor.execute("""
                UPDATE TBL_StatusMaquina 
                SET DataHoraFim = GETDATE(),
                    DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, GETDATE())
                WHERE IDStatus = ?
            """, (id_status_atual,))

            cursor.execute("""
                INSERT INTO TBL_StatusMaquina 
                (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, IDMotivoParada, DescricaoStatus)
                VALUES (?, 0, GETDATE(), GETDATE(), ?, ?, 'Parada')
            """, (id_maquina, id_turno, id_motivo))

    else:
        cursor.execute("""
            INSERT INTO TBL_StatusMaquina 
            (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, IDMotivoParada, DescricaoStatus)
            VALUES (?, 0, GETDATE(), GETDATE(), ?, ?, 'Parada')
        """, (id_maquina, id_turno, id_motivo))

    conn.commit()
    return jsonify({'mensagem': 'Motivo de parada registrado com sucesso.'})
    
@app.route('/cadastro_grupo_motivo_refugo', methods=['GET', 'POST'])
def cadastro_grupo_motivo_refugo():
    id_grupo = request.args.get('id')
    grupo_editar = None

    if request.method == 'POST':
        id_grupo = request.form.get('id_grupo')
        codigo = request.form['codigo']
        nome = request.form['nome']
        descricao = request.form['descricao']
        ativo = 'ativo' in request.form

        if id_grupo:
            cursor.execute("""
                UPDATE TBL_GrupoRefugo
                SET Codigo = ?, NomeGrupo = ?, Descricao = ?, Ativo = ?
                WHERE IDGrupoMotivoRefugo = ?
            """, codigo, nome, descricao, ativo, id_grupo)
        else:
            cursor.execute("""
                INSERT INTO TBL_GrupoRefugo (Codigo, NomeGrupo, Descricao, Ativo)
                VALUES (?, ?, ?, ?)
            """, codigo, nome, descricao, ativo)

        conn.commit()
        return redirect('/cadastro_grupo_motivo_refugo')

    if id_grupo:
        cursor.execute("SELECT * FROM TBL_GrupoRefugo WHERE IDGrupoMotivoRefugo = ?", id_grupo)
        grupo_editar = cursor.fetchone()

    cursor.execute("SELECT * FROM TBL_GrupoRefugo")
    grupos = cursor.fetchall()

    return render_template('cadastro_grupo_motivo_refugo.html', grupos=grupos, grupo_editar=grupo_editar)

@app.route('/cadastro_motivo_refugo', methods=['GET', 'POST'])
def cadastro_motivo_refugo():
    id_edicao = request.args.get('id')
    motivo_editar = None

    if request.method == 'POST':
        id_motivo = request.form.get('id_motivo')
        codigo = request.form['codigo']
        descricao = request.form['descricao']
        id_grupo = request.form['id_grupo']
        ativo = 'ativo' in request.form

        if id_motivo:
            cursor.execute("""
                UPDATE TBL_MotivoRefugo
                SET Codigo = ?, Descricao = ?, IDGrupoMotivoRefugo = ?, Ativo = ?
                WHERE IDMotivoRefugo = ?
            """, codigo, descricao, id_grupo, ativo, id_motivo)
        else:
            cursor.execute("""
                INSERT INTO TBL_MotivoRefugo (Codigo, Descricao, IDGrupoMotivoRefugo, Ativo)
                VALUES (?, ?, ?, ?)
            """, codigo, descricao, id_grupo, ativo)

        conn.commit()
        return redirect('/cadastro_motivo_refugo')

    if id_edicao:
        cursor.execute("SELECT * FROM TBL_MotivoRefugo WHERE IDMotivoRefugo = ?", id_edicao)
        motivo_editar = cursor.fetchone()

    cursor.execute("SELECT * FROM TBL_GrupoRefugo")
    grupos = cursor.fetchall()

    cursor.execute("""
        SELECT M.*, G.NomeGrupo
        FROM TBL_MotivoRefugo M
        LEFT JOIN TBL_GrupoRefugo G ON M.IDGrupoMotivoRefugo = G.IDGrupoMotivoRefugo
    """)
    motivos = cursor.fetchall()

    return render_template('cadastro_motivo_refugo.html', motivos=motivos, motivo_editar=motivo_editar, grupos=grupos)

@app.route('/registrar_producao_manual', methods=['POST'])
def registrar_producao_manual():
    data = request.get_json()
    id_maquina = data.get('id_maquina')
    tipo = data.get('tipo')  # 'unidade' ou 'caixa'
    quantidade = float(data.get('quantidade'))

    # Passo 1: buscar execução ativa
    cursor.execute("""
        SELECT TOP 1 
            E.IDExecucao, O.IDOrdem, O.IDProduto, P.FatorMultiplicacao, P.UnidadesPorCaixa
        FROM TBL_ExecucaoOP E
        INNER JOIN TBL_OrdemProducao O ON E.IDOrdem = O.IDOrdem
        INNER JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
        WHERE E.IDMaquina = ? AND E.DataHoraFim IS NULL
        ORDER BY E.IDExecucao DESC
    """, id_maquina)
    resultado = cursor.fetchone()

    if not resultado:
        return jsonify({"mensagem": "Nenhuma ordem de produção ativa para esta máquina."})

    id_execucao, id_ordem, id_produto, fator, unidades_por_caixa = resultado

    # Passo 2: buscar IDTipo (tipo do recurso) na tabela Recursos
    cursor.execute("""
        SELECT IDTipo 
        FROM TBL_Recurso 
        WHERE IDMaquina = ?
    """, id_maquina)
    tipo_recurso_result = cursor.fetchone()
    if tipo_recurso_result:
        id_tipo_recurso = tipo_recurso_result[0]
    else:
        id_tipo_recurso = None  # Se não tiver, fica NULL

    # Passo 3: buscar IDTurno e IDOperador do último evento automático
    cursor.execute("""
        SELECT TOP 1 IDTurno, IDOperador
        FROM PLN_PRD.dbo.EventosProducao
        WHERE IDExecucao = ? AND OrigemEvento = 'AUTOMATICO'
        ORDER BY DataHoraEvento DESC
    """, id_execucao)
    evento_result = cursor.fetchone()
    if evento_result:
        id_turno, id_operador = evento_result
    else:
        id_turno, id_operador = None, None

    # Passo 3.1: Se não achou turno, identificar pelo horário atual
    if not id_turno:
        agora = datetime.now().time()
        cursor.execute("""
            SELECT IDTurno 
            FROM TBL_Turno 
            WHERE 
                (HoraInicio <= ? AND HoraFim > ?) 
                OR 
                (HoraInicio > HoraFim AND (HoraInicio <= ? OR HoraFim > ?))
        """, agora, agora, agora, agora)
        turno_result = cursor.fetchone()
        if turno_result:
            id_turno = turno_result[0]
        else:
            id_turno = None  # Se não encontrou turno

    # Passo 4: converter quantidade
    if tipo == "unidade":
        quantidade_unidades = quantidade
    elif tipo == "caixa":
        quantidade_unidades = quantidade * unidades_por_caixa
    else:
        return jsonify({"mensagem": "Tipo inválido."})

    # Passo 5: inserir evento
    cursor.execute("""
        INSERT INTO PLN_PRD.dbo.EventosProducao (
            IDExecucao, IDRecurso, IDTipoRecurso, IDOrdemProducao, IDTurno, IDOperador,
            IDTipoEvento, Quantidade, TipoValor, OrigemEvento, DataHoraEvento
        )
        VALUES (?, ?, ?, ?, ?, ?, 1, ?, 'BOA', 'MANUAL', GETDATE())
    """, id_execucao, id_maquina, id_tipo_recurso, id_ordem, id_turno, id_operador, quantidade_unidades)

    conn.commit()

    return jsonify({"mensagem": "Produção registrada com sucesso."})

#############NOVAS ROTAS

@app.route('/modelagem')
def modelagem():
    return render_template('modelagem.html')
    
@app.route('/cadastro_sistema')
def cadastro_sistema():
    return render_template('cadastro_sistema.html')

    
@app.route('/cadastro_empresa', methods=['GET', 'POST'])
def cadastro_empresa():
    if request.method == 'POST':
        nome = request.form['nome']
        codigo = request.form['codigo']
        descricao = request.form['descricao']
        ativo = 1 if 'ativo' in request.form else 0

        cursor.execute("""
            INSERT INTO TBL_Empresa (Nome, Codigo, Descricao, Ativo, DtCriacao)
            VALUES (?, ?, ?, ?, GETDATE())
        """, (nome, codigo, descricao, ativo))
        conn.commit()

    cursor.execute("SELECT IDEmpresa, Nome, Codigo, Descricao, Ativo FROM TBL_Empresa")
    empresas = cursor.fetchall()

    return render_template('cadastro_empresa.html', empresas=empresas)

@app.route('/cadastro_setor', methods=['GET', 'POST'])
def cadastro_setor():
    id_edicao = request.args.get('id')
    setor_editar = None
    
    if request.method == 'POST':
        nome = request.form['nome']
        codigo = request.form['codigo']
        descricao = request.form['descricao']
        ativo = 1 if 'ativo' in request.form else 0
        id_empresa = request.form['id_empresa']
        id_area = request.form['id_area']

        if id_edicao:
            # Atualização
            cursor.execute("""
                UPDATE TBL_Setor 
                SET Nome = ?, Codigo = ?, Descricao = ?, Ativo = ?, IDEmpresa = ?, IDArea = ?
                WHERE IDSetor = ?
            """, (nome, codigo, descricao, ativo, id_empresa, id_area, id_edicao))
        else:
            # Inserção
            cursor.execute("""
                INSERT INTO TBL_Setor (Nome, Codigo, Descricao, Ativo, DtCriacao, IDEmpresa, IDArea)
                VALUES (?, ?, ?, ?, GETDATE(), ?, ?)
            """, (nome, codigo, descricao, ativo, id_empresa, id_area))
        
        conn.commit()
        return redirect(url_for('cadastro_setor'))

    # Buscar setor para edição, se houver ID
    if id_edicao:
        cursor.execute("SELECT * FROM TBL_Setor WHERE IDSetor = ?", (id_edicao,))
        setor_editar = cursor.fetchone()

    # Consulta para obter todos os setores com nomes de empresa e área
    cursor.execute("""
        SELECT S.IDSetor, S.Nome, S.Codigo, S.Descricao, S.Ativo, 
               S.IDEmpresa, E.Nome AS NomeEmpresa,
               S.IDArea, A.Nome AS NomeArea
        FROM TBL_Setor S
        LEFT JOIN TBL_Empresa E ON S.IDEmpresa = E.IDEmpresa
        LEFT JOIN TBL_Area A ON S.IDArea = A.IDArea
        ORDER BY S.Nome
    """)
    setores = cursor.fetchall()

    # Consulta para obter empresas ativas
    cursor.execute("SELECT IDEmpresa, Nome FROM TBL_Empresa WHERE Ativo = 1 ORDER BY Nome")
    empresas = cursor.fetchall()

    # Consulta para obter áreas ativas
    cursor.execute("SELECT IDArea, Nome, IDEmpresa FROM TBL_Area WHERE Ativo = 1 ORDER BY Nome")
    areas = cursor.fetchall()
    
    # Verificação de debug
    logger.debug(f"Áreas encontradas: {len(areas)}")
    for area in areas:
        logger.debug(f"  - ID: {area.IDArea}, Nome: {area.Nome}")

    return render_template('cadastro_setor.html', 
                          setores=setores, 
                          empresas=empresas, 
                          areas=areas,
                          setor_editar=setor_editar)

@app.route('/cadastro_area', methods=['GET', 'POST'])
def cadastro_area():
    if request.method == 'POST':
        nome = request.form['nome']
        codigo = request.form['codigo']
        descricao = request.form['descricao']
        ativo = 1 if 'ativo' in request.form else 0
        id_empresa = request.form['id_empresa']

        cursor.execute("""
            INSERT INTO TBL_Area (Nome, Codigo, Descricao, Ativo, DtCriacao, IDEmpresa)
            VALUES (?, ?, ?, ?, GETDATE(), ?)
        """, (nome, codigo, descricao, ativo, id_empresa))
        conn.commit()

    cursor.execute("SELECT IDArea, Nome, Codigo, Descricao, Ativo, IDEmpresa FROM TBL_Area")
    areas = cursor.fetchall()

    cursor.execute("SELECT IDEmpresa, Nome FROM TBL_Empresa")
    empresas = cursor.fetchall()

    return render_template('cadastro_area.html', areas=areas, empresas=empresas)

@app.route('/cadastro_grupo_parada', methods=['GET', 'POST'])
def cadastro_grupo_parada():
    id_grupo = request.args.get('id')
    grupo_editar = None

    if request.method == 'POST':
        nome = request.form['nome']
        descricao = request.form['descricao']
        ativo = 'ativo' in request.form

        if id_grupo:
            cursor.execute("""
                UPDATE TBL_GrupoParada
                SET NomeGrupo = ?, Descricao = ?, Ativo = ?
                WHERE IDGrupoParada = ?
            """, nome, descricao, ativo, id_grupo)
        else:
            cursor.execute("""
                INSERT INTO TBL_GrupoParada (NomeGrupo, Descricao, Ativo)
                VALUES (?, ?, ?)
            """, nome, descricao, ativo)
        conn.commit()
        return redirect('/cadastro_grupo_parada')

    if id_grupo:
        cursor.execute("SELECT * FROM TBL_GrupoParada WHERE IDGrupoParada = ?", id_grupo)
        grupo_editar = cursor.fetchone()

    cursor.execute("SELECT * FROM TBL_GrupoParada")
    grupos = cursor.fetchall()

    return render_template('cadastro_grupo_parada.html', grupos=grupos, grupo_editar=grupo_editar)

@app.route('/cadastro_motivo_parada', methods=['GET', 'POST'])
def cadastro_motivo_parada():
    id_motivo = request.args.get('id')
    motivo_editar = None

    if request.method == 'POST':
        id_motivo = request.form.get('id_motivo')
        codigo = request.form['codigo']
        descricao = request.form['descricao']
        planejada = request.form['planejada']
        ativo = 'ativo' in request.form

        if id_motivo:
            cursor.execute("""
                UPDATE TBL_MotivoParada
                SET Codigo = ?, Descricao = ?, FlgPlanejada = ?, Ativo = ?
                WHERE IDMotivoParada = ?
            """, codigo, descricao, planejada, ativo, id_motivo)
        else:
            cursor.execute("""
                INSERT INTO TBL_MotivoParada (Codigo, Descricao, FlgPlanejada, Ativo)
                VALUES (?, ?, ?, ?)
            """, codigo, descricao, planejada, ativo)

        conn.commit()
        return redirect('/cadastro_motivo_parada')

    if id_motivo:
        cursor.execute("SELECT * FROM TBL_MotivoParada WHERE IDMotivoParada = ?", id_motivo)
        motivo_editar = cursor.fetchone()

    cursor.execute("SELECT * FROM TBL_MotivoParada")
    motivos = cursor.fetchall()

    return render_template('cadastro_motivo_parada.html', motivos=motivos, motivo_editar=motivo_editar)

@app.route('/cadastro_turno', methods=['GET', 'POST'])
def cadastro_turno():
    id_turno = request.args.get('id')
    turno_editar = None

    if request.method == 'POST':
        id_turno = request.form.get('id_turno')
        codigo = request.form['codigo']
        nome = request.form['nome']
        hora_inicio = request.form['hora_inicio']
        hora_fim = request.form['hora_fim']

        dias_semana = []
        for dia in ['dom', 'seg', 'ter', 'qua', 'qui', 'sex', 'sab']:
            if dia in request.form:
                dias_semana.append(dia.capitalize())

        semana = ','.join(dias_semana)
        todos = 1 if 'todos' in request.form else 0
        ativo = 1 if 'ativo' in request.form else 0

        if id_turno:
            cursor.execute("""
                UPDATE TBL_Turno
                SET Codigo = ?, NomeTurno = ?, HoraInicio = ?, HoraFim = ?, Semana = ?, Todos = ?, Ativo = ?
                WHERE IDTurno = ?
            """, codigo, nome, hora_inicio, hora_fim, semana, todos, ativo, id_turno)
        else:
            cursor.execute("""
                INSERT INTO TBL_Turno (Codigo, NomeTurno, HoraInicio, HoraFim, Semana, Todos, Ativo)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """, codigo, nome, hora_inicio, hora_fim, semana, todos, ativo)

        conn.commit()
        return redirect('/cadastro_turno')

    if id_turno:
        cursor.execute("SELECT * FROM TBL_Turno WHERE IDTurno = ?", id_turno)
        turno_editar = cursor.fetchone()

    cursor.execute("SELECT * FROM TBL_Turno")
    turnos = cursor.fetchall()

    return render_template('cadastro_turno.html', turnos=turnos, turno_editar=turno_editar)
    
#####TELA PRODUÇÃO
@app.route('/cadastro_producao')
def cadastro_producao():
    return render_template('cadastro_producao.html')
    
#### relatorios
@app.route('/relatorios')
def relatorios():
    return render_template('relatorios.html')

def validar_data(data_str):
    try:
        return datetime.strptime(data_str, '%Y-%m-%d')
    except:
        return None

@app.route('/relatorio_refugos', methods=['GET', 'POST'])
def relatorio_refugos():
    agrupado = []

    if request.method == 'POST':
        data_inicio = request.form.get('data_inicio')
        data_fim = request.form.get('data_fim')
        codigo_ordem = request.form.get('codigo_ordem')

        data_inicio_dt = validar_data(data_inicio)
        data_fim_dt = validar_data(data_fim)

        # Adiciona 1 dia à data final para pegar até 23:59:59
        if data_fim_dt:
            data_fim_dt = data_fim_dt + timedelta(days=1)

        query = """
        SELECT 
            E.DataHoraEvento,
            R.NomeMaquina,
            E.Quantidade,
            MR.Descricao AS MotivoRefugo,
            O.CodigoOrdem,
            P.CodigoProduto,
            P.NomeProduto
        FROM TBL_EventoProducao E
        JOIN TBL_ExecucaoOP EX ON EX.IDExecucao = E.IDExecucao
        JOIN TBL_OrdemProducao O ON O.IDOrdem = EX.IDOrdem
        JOIN TBL_Produto P ON O.IDProduto = P.IDProduto
        JOIN TBL_Recurso R ON R.IDMaquina = EX.IDMaquina
        LEFT JOIN TBL_MotivoRefugo MR ON MR.IDMotivoRefugo = E.IDMotivoRefugo
        WHERE E.IDTipoEvento = 2 AND E.TipoValor = 'refugo'
        """

        params = []

        if data_inicio_dt:
            query += " AND E.DataHoraEvento >= ?"
            params.append(data_inicio_dt)

        if data_fim_dt:
            query += " AND E.DataHoraEvento < ?"  # ATENÇÃO: usa < com data_fim + 1
            params.append(data_fim_dt)

        if codigo_ordem:
            query += " AND O.CodigoOrdem = ?"
            params.append(codigo_ordem)

        cursor.execute(query, params)
        rows = cursor.fetchall()

        # Agrupar por ordem/produto
        agrupado_dict = {}
        for row in rows:
            chave = (row.CodigoOrdem, f"{row.CodigoProduto} - {row.NomeProduto}")
            if chave not in agrupado_dict:
                agrupado_dict[chave] = {
                    'ordem': row.CodigoOrdem,
                    'produto': f"{row.CodigoProduto} - {row.NomeProduto}",
                    'total': 0,
                    'refugos': []
                }
            agrupado_dict[chave]['refugos'].append(row)
            agrupado_dict[chave]['total'] += row.Quantidade

        agrupado = list(agrupado_dict.values())

    return render_template('relatorio_refugos.html', agrupado=agrupado)

def validar_data(data_str):
    try:
        return datetime.strptime(data_str, '%Y-%m-%d')
    except:
        return None

@app.route('/relatorio_paradas', methods=['GET', 'POST'])
def relatorio_paradas():
    agrupado = []

    if request.method == 'POST':
        data_inicio = request.form.get('data_inicio')
        data_fim = request.form.get('data_fim')

        inicio_dt = validar_data(data_inicio)
        fim_dt = validar_data(data_fim)
        if fim_dt:
            fim_dt += timedelta(days=1)

        query = """
        SELECT 
            SM.DataHoraInicio,
            SM.DataHoraFim,
            ROUND(SM.DiffStatusSegundos / 3600.0, 2) AS DuracaoHoras,
            MP.Descricao AS MotivoParada,
            R.NomeMaquina
        FROM TBL_StatusMaquina SM
        JOIN TBL_Recurso R ON R.IDMaquina = SM.IDMaquina
        LEFT JOIN TBL_MotivoParada MP ON MP.IDMotivoParada = SM.IDMotivoParada
        WHERE 1=1
        """

        params = []

        if inicio_dt:
            query += " AND SM.DataHoraInicio >= ?"
            params.append(inicio_dt)

        if fim_dt:
            query += " AND SM.DataHoraInicio < ?"
            params.append(fim_dt)

        cursor.execute(query, params)
        rows = cursor.fetchall()

        # Agrupamento por máquina
        agrupado_dict = {}
        for row in rows:
            maquina = row.NomeMaquina
            if maquina not in agrupado_dict:
                agrupado_dict[maquina] = {
                    'maquina': maquina,
                    'total': 0,
                    'paradas': []
                }
            agrupado_dict[maquina]['paradas'].append(row)
            agrupado_dict[maquina]['total'] += row.DuracaoHoras or 0

        agrupado = list(agrupado_dict.values())

    return render_template('relatorio_paradas.html', agrupado=agrupado)

@app.route('/cadastro_grupo_alarme', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_grupo_alarme')
def cadastro_grupo_alarme():
    id_grupo = request.args.get('id')
    grupo_editar = None

    if request.method == 'POST':
        id_grupo = request.form.get('id_grupo')
        codigo = request.form['codigo']
        nome = request.form['nome']
        descricao = request.form['descricao']
        ativo = 1 if 'ativo' in request.form else 0

        if id_grupo:
            # Atualização
            cursor.execute("""
                UPDATE TBL_GrupoAlarme
                SET Codigo = ?, Nome = ?, Descricao = ?, Ativo = ?, DataAtualizacao = GETDATE()
                WHERE IDGrupoAlarme = ?
            """, (codigo, nome, descricao, ativo, id_grupo))
        else:
            # Inserção
            cursor.execute("""
                INSERT INTO TBL_GrupoAlarme (Codigo, Nome, Descricao, Ativo, DataCriacao)
                VALUES (?, ?, ?, ?, GETDATE())
            """, (codigo, nome, descricao, ativo))

        conn.commit()
        return redirect(url_for('cadastro_grupo_alarme'))

    # Buscar grupo para edição, se houver ID
    if id_grupo:
        cursor.execute("SELECT * FROM TBL_GrupoAlarme WHERE IDGrupoAlarme = ?", (id_grupo,))
        grupo_editar = cursor.fetchone()

    # Buscar todos os grupos
    cursor.execute("SELECT * FROM TBL_GrupoAlarme ORDER BY Nome")
    grupos = cursor.fetchall()

    return render_template('cadastro_grupo_alarme.html', grupos=grupos, grupo_editar=grupo_editar)
    
@app.route('/alterar_status_grupo_alarme/<int:id_grupo>/<int:status>')
@login_requerido
@permissao_requerida('/cadastro_grupo_alarme')
def alterar_status_grupo_alarme(id_grupo, status):
    cursor.execute("""
        UPDATE TBL_GrupoAlarme
        SET Ativo = ?, DataAtualizacao = GETDATE()
        WHERE IDGrupoAlarme = ?
    """, (status, id_grupo))
    conn.commit()
    return redirect(url_for('cadastro_grupo_alarme'))
    
def verificar_inatividade_maquinas():
    try:
        # Obter máquinas ativas
        cursor.execute("SELECT IDMaquina FROM TBL_Recurso WHERE Ativo = 1")
        maquinas_ativas = cursor.fetchall()
        
        for maquina in maquinas_ativas:
            id_maquina = maquina[0]
            
            # Verificar o último pulso registrado para esta máquina
            cursor.execute("""
                SELECT TOP 1 DataHoraEvento
                FROM TBL_EventoProducao
                WHERE IDMaquina = ?
                ORDER BY DataHoraEvento DESC
            """, id_maquina)
            
            ultimo_pulso = cursor.fetchone()
            
            # Verificar o status atual da máquina
            cursor.execute("""
                SELECT TOP 1 Status
                FROM TBL_StatusMaquina
                WHERE IDMaquina = ?
                ORDER BY DataHoraRegistro DESC
            """, id_maquina)
            
            status_atual = cursor.fetchone()
            
            if ultimo_pulso:
                tempo_desde_ultimo_pulso = (datetime.now() - ultimo_pulso.DataHoraEvento).total_seconds()
                
                # Se não houver pulso nos últimos 10 segundos e a máquina não estiver já em parada, registrar parada
                if tempo_desde_ultimo_pulso > 10 and (not status_atual or status_atual.Status == 1):
                    logger.warning(f"Máquina {id_maquina} sem pulso há {tempo_desde_ultimo_pulso:.2f} segundos. Registrando parada.")
                    registrar_parada_por_inatividade(id_maquina)
            else:
                logger.warning(f"Máquina {id_maquina} não tem registros de pulso.")
                
    except Exception as e:
        logger.error(f"Erro ao verificar inatividade das máquinas: {str(e)}")
        import traceback
        logger.error(traceback.format_exc())   

def registrar_parada_por_inatividade(id_maquina):
    try:
        # Obter timestamp atual
        timestamp = datetime.now()
        
        # Identificar o turno atual
        id_turno_atual = identificar_turno()
        
        # ID do motivo de parada automática (ajuste conforme necessário)
        id_motivo_parada_automatica = 11  # Substitua pelo ID correto do seu banco de dados
        
        # Verificar o último status registrado para esta máquina
        cursor.execute("""
            SELECT TOP 1 IDStatus, Status, DataHoraInicio 
            FROM TBL_StatusMaquina 
            WHERE IDMaquina = ? 
            ORDER BY DataHoraRegistro DESC
        """, id_maquina)
        
        ultimo_status_db = cursor.fetchone()
        
        # Se o último status for "em execução", fechá-lo
        if ultimo_status_db and ultimo_status_db.Status == 1:
            cursor.execute("""
                UPDATE TBL_StatusMaquina 
                SET DataHoraFim = ?, 
                    DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, ?)
                WHERE IDStatus = ?
            """, timestamp, timestamp, ultimo_status_db.IDStatus)
        
        # Inserir o novo status de parada na TBL_StatusMaquina
        cursor.execute("""
            INSERT INTO TBL_StatusMaquina 
            (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDMotivoParada, IDTurno, ObsEvento, DescricaoStatus) 
            VALUES (?, 0, ?, ?, ?, ?, ?, ?)
        """, id_maquina, timestamp, timestamp, id_motivo_parada_automatica, id_turno_atual, "Parada automática por inatividade", "Parada")
        
        # Inserir no histórico de eventos (TBL_EventoStatus)
        cursor.execute("""
            INSERT INTO TBL_EventoStatus 
            (IDMaquina, Status, DataHoraEvento, IDMotivoParada, ObsEvento) 
            VALUES (?, 0, ?, ?, ?)
        """, id_maquina, timestamp, id_motivo_parada_automatica, "Parada automática por inatividade")
        
        conn.commit()
        logger.info(f"Parada automática registrada para máquina {id_maquina}")
        
    except Exception as e:
        conn.rollback()
        logger.error(f"Erro ao registrar parada automática: {str(e)}")
        import traceback
        logger.error(traceback.format_exc())   

# Função para executar verificação de inatividade em um thread separado
def verificar_inatividade_periodicamente():
    while True:
        try:
            verificar_inatividade_maquinas()
            time.sleep(5)  # Verificar a cada 5 segundos
        except Exception as e:
            logger.error(f"Erro no thread de verificação de inatividade: {str(e)}")
            time.sleep(5)  # Continuar tentando mesmo em caso de erro

# Iniciar o thread de verificação de inatividade
thread_inatividade = threading.Thread(target=verificar_inatividade_periodicamente, daemon=True)
thread_inatividade.start()        
    
@app.route('/cadastro_motivo_alarme', methods=['GET', 'POST'])
@login_requerido
@permissao_requerida('/cadastro_motivo_alarme')
def cadastro_motivo_alarme():
    id_motivo = request.args.get('id')
    motivo_editar = None
    
    # Tipos de alarme predefinidos
    tipos_alarme = ['Crítico', 'Alerta', 'Informativo', 'Manutenção', 'Segurança']

    if request.method == 'POST':
        id_motivo = request.form.get('id_motivo')
        codigo = request.form['codigo']
        nome = request.form['nome']
        descricao = request.form['descricao']
        tipo_alarme = request.form['tipo_alarme']
        id_grupo = request.form['id_grupo']
        ativo = 1 if 'ativo' in request.form else 0

        if id_motivo:
            # Atualização
            cursor.execute("""
                UPDATE TBL_MotivoAlarme
                SET Codigo = ?, Nome = ?, Descricao = ?, TipoAlarme = ?, 
                    IDGrupoAlarme = ?, Ativo = ?, DataAtualizacao = GETDATE()
                WHERE IDMotivoAlarme = ?
            """, (codigo, nome, descricao, tipo_alarme, id_grupo, ativo, id_motivo))
        else:
            # Inserção
            cursor.execute("""
                INSERT INTO TBL_MotivoAlarme 
                (Codigo, Nome, Descricao, TipoAlarme, IDGrupoAlarme, Ativo, DataCriacao)
                VALUES (?, ?, ?, ?, ?, ?, GETDATE())
            """, (codigo, nome, descricao, tipo_alarme, id_grupo, ativo))

        conn.commit()
        return redirect(url_for('cadastro_motivo_alarme'))

    
    # Buscar motivo para edição, se houver ID
    if id_motivo:
        cursor.execute("""
            SELECT * FROM TBL_MotivoAlarme WHERE IDMotivoAlarme = ?
        """, (id_motivo,))
        motivo_editar = cursor.fetchone()

    # Buscar todos os grupos de alarme ativos
    cursor.execute("""
        SELECT IDGrupoAlarme, Nome FROM TBL_GrupoAlarme 
        WHERE Ativo = 1 
        ORDER BY Nome
    """)
    grupos = cursor.fetchall()

    # Buscar todos os motivos com informações do grupo
    cursor.execute("""
        SELECT M.*, G.Nome AS NomeGrupo
        FROM TBL_MotivoAlarme M
        LEFT JOIN TBL_GrupoAlarme G ON M.IDGrupoAlarme = G.IDGrupoAlarme
        ORDER BY M.Nome
    """)
    motivos = cursor.fetchall()

    return render_template('cadastro_motivo_alarme.html', 
                          motivos=motivos, 
                          motivo_editar=motivo_editar, 
                          grupos=grupos,
                          tipos_alarme=tipos_alarme)

@app.route('/alterar_status_motivo_alarme/<int:id_motivo>/<int:status>')
@login_requerido
@permissao_requerida('/cadastro_motivo_alarme')
def alterar_status_motivo_alarme(id_motivo, status):
    cursor.execute("""
        UPDATE TBL_MotivoAlarme
        SET Ativo = ?, DataAtualizacao = GETDATE()
        WHERE IDMotivoAlarme = ?
    """, (status, id_motivo))
    conn.commit()
    return redirect(url_for('cadastro_motivo_alarme'))
# Rota para adicionar produção

# Rota para adicionar produção
# Rota para adicionar produção
@app.route('/adicionar_producao', methods=['POST'])
def adicionar_producao():
    try:
        id_maquina = request.form.get('id_maquina', type=int)
        tipo = request.form.get('tipo')  # 'unidade' ou 'caixa'
        quantidade = request.form.get('quantidade', type=int)
        observacao = request.form.get('observacao')
        
        # Validar os dados
        if not id_maquina or not tipo or not quantidade:
            return jsonify({'success': False, 'message': 'Dados incompletos'})
        
        # Identificar o turno atual
        id_turno_atual = identificar_turno()
        
        # Obter a ordem ativa para a máquina
        cursor.execute("""
            SELECT TOP 1 E.IDOrdem, E.IDExecucao
            FROM TBL_ExecucaoOP E
            WHERE E.IDMaquina = ?
            AND E.DataHoraFim IS NULL
            AND E.Status = 'Em Execucao'
            ORDER BY E.IDExecucao DESC
        """, id_maquina)
        
        row_ordem = cursor.fetchone()
        
        if not row_ordem:
            return jsonify({'success': False, 'message': 'Nenhuma ordem ativa para esta máquina'})
        
        id_ordem = row_ordem.IDOrdem
        id_execucao = row_ordem.IDExecucao
        
        # Inserir o registro de produção
        tipo_valor = 'BOA'
        if tipo == 'caixa':
            # Se for caixa, precisamos converter para unidades
            cursor.execute("""
                SELECT P.UnidadesporCaixa
                FROM TBL_OrdemProducao O
                JOIN TBL_Produto P ON P.IDProduto = O.IDProduto
                WHERE O.IDOrdem = ?
            """, id_ordem)
            
            row_produto = cursor.fetchone()
            if not row_produto or not row_produto.UnidadesporCaixa:
                return jsonify({'success': False, 'message': 'Produto sem definição de unidades por caixa'})
            
            # Converter caixas para unidades
            quantidade_unidades = quantidade * row_produto.UnidadesporCaixa
            
            cursor.execute("""
                INSERT INTO TBL_EventoProducao (
                    IDRecurso, IDOrdemProducao, IDTurno, IDExecucao,
                    DataHora, TipoValor, Quantidade, Observacao
                ) VALUES (?, ?, ?, ?, GETDATE(), ?, ?, ?)
            """, (
                id_maquina, id_ordem, id_turno_atual, id_execucao,
                tipo_valor, quantidade_unidades, observacao
            ))
        else:
            # Inserir diretamente as unidades
            cursor.execute("""
                INSERT INTO TBL_EventoProducao (
                    IDRecurso, IDOrdemProducao, IDTurno, IDExecucao,
                    DataHora, TipoValor, Quantidade, Observacao
                ) VALUES (?, ?, ?, ?, GETDATE(), ?, ?, ?)
            """, (
                id_maquina, id_ordem, id_turno_atual, id_execucao,
                tipo_valor, quantidade, observacao
            ))
        
        conn.commit()
        
        return jsonify({'success': True})
    
    except Exception as e:
        conn.rollback()
        print(f"Erro ao adicionar produção: {e}")
        return jsonify({'success': False, 'message': str(e)})

@app.route('/adicionar_refugo', methods=['POST'])
def adicionar_refugo():
    try:
        id_maquina = request.form.get('id_maquina', type=int)
        quantidade = request.form.get('quantidade', type=int)
        motivo_refugo = request.form.get('motivo_refugo', type=int)
        observacao = request.form.get('observacao')
        
        # Validar os dados
        if not id_maquina or not quantidade or not motivo_refugo:
            return jsonify({'success': False, 'message': 'Dados incompletos'})
        
        # Identificar o turno atual
        id_turno_atual = identificar_turno()
        
        # Obter a ordem ativa para a máquina
        cursor.execute("""
            SELECT TOP 1 E.IDOrdem, E.IDExecucao
            FROM TBL_ExecucaoOP E
            WHERE E.IDMaquina = ?
            AND E.DataHoraFim IS NULL
            AND E.Status = 'Em Execucao'
            ORDER BY E.IDExecucao DESC
        """, id_maquina)
        
        row_ordem = cursor.fetchone()
        
        if not row_ordem:
            return jsonify({'success': False, 'message': 'Nenhuma ordem ativa para esta máquina'})
        
        id_ordem = row_ordem.IDOrdem
        id_execucao = row_ordem.IDExecucao
        
        # Obter apenas o IDSetor do recurso (máquina)
        cursor.execute("""
            SELECT IDSetor
            FROM TBL_Recurso
            WHERE IDMaquina = ?
        """, id_maquina)
        
        row_recurso = cursor.fetchone()
        id_setor = row_recurso.IDSetor if row_recurso else None
        
        # Obter o ID do tipo de evento para refugo
        id_tipo_evento = None
        try:
            cursor.execute("""
                SELECT TOP 1 IDTipoEvento 
                FROM TBL_TipoEvento 
                WHERE Descricao LIKE '%Refugo%' OR Descricao LIKE '%Perda%'
            """)
            row_tipo = cursor.fetchone()
            if row_tipo:
                id_tipo_evento = row_tipo.IDTipoEvento
        except:
            # Se a tabela não existir ou ocorrer outro erro, continuamos sem o IDTipoEvento
            pass
        
        # Inserir o registro de refugo sem as colunas IDEmpresa e IDArea
        cursor.execute("""
            INSERT INTO TBL_EventoProducao (
                IDExecucao,
                IDTipoEvento,
                Quantidade,
                DataHoraEvento,
                IDRecurso,
                IDOrdemProducao,
                IDTurno,
                TipoValor,
                ObsEvento,
                IDMotivoRefugo,
                OrigemEvento,
                IDSetor
            ) VALUES (
                ?, ?, ?, GETDATE(), ?, ?, ?, 'REFUGO', ?, ?, 'MANUAL', ?
            )
        """, (
            id_execucao,
            id_tipo_evento,
            quantidade,
            id_maquina,
            id_ordem,
            id_turno_atual,
            observacao,
            motivo_refugo,
            id_setor
        ))
        
        conn.commit()
        
        return jsonify({'success': True})
    
    except Exception as e:
        conn.rollback()
        print(f"Erro ao adicionar refugo: {e}")
        return jsonify({'success': False, 'message': str(e)})


def identificar_turno():
    """
    Identifica o turno atual com base na hora atual.
    Retorna o ID do turno atual ou None se não houver turno ativo.
    """
    try:
        hora_atual = datetime.now().time()
        
        # Consulta para encontrar o turno atual
        cursor.execute("""
            SELECT IDTurno
            FROM TBL_Turno
            WHERE 
                (
                    (HoraInicio <= HoraFim AND ? BETWEEN HoraInicio AND HoraFim) OR
                    (HoraInicio > HoraFim AND (? >= HoraInicio OR ? <= HoraFim))
                )
                AND Ativo = 1
        """, (hora_atual, hora_atual, hora_atual))
        
        row = cursor.fetchone()
        return row.IDTurno if row else None
        
    except Exception as e:
        print(f"Erro ao identificar turno: {e}")
        return None
        
        
     
def obter_disponibilidade_turno(id_maquina, id_turno=1):
    try:
        logger.info(f"Calculando disponibilidade para máquina {id_maquina} no turno {id_turno}")
        
        # Obter informações do turno
        cursor.execute("""
            SELECT HoraInicio, HoraFim
            FROM TBL_Turno
            WHERE IDTurno = ?
        """, id_turno)

        turno = cursor.fetchone()
        if not turno:
            logger.warning(f"Turno ID {id_turno} não encontrado no banco de dados")
            return {
                'TempoRodando': 0,
                'TempoParado': 0,
                'Disponibilidade_Pct': 0.0
            }

        logger.info(f"Turno encontrado: Início {turno.HoraInicio}, Fim {turno.HoraFim}")
        
        # Obter hora atual
        agora = datetime.now()
        logger.info(f"Hora atual: {agora}")
        
        # Extrair hora e minuto do início e fim do turno
        # Tratando tanto string quanto objeto time
        if isinstance(turno.HoraInicio, str):
            hora_inicio, minuto_inicio = map(int, turno.HoraInicio.split(':'))
        else:
            hora_inicio = turno.HoraInicio.hour
            minuto_inicio = turno.HoraInicio.minute
    
        if isinstance(turno.HoraFim, str):
            hora_fim, minuto_fim = map(int, turno.HoraFim.split(':'))
        else:
            hora_fim = turno.HoraFim.hour
            minuto_fim = turno.HoraFim.minute
        
        # Criar objetos datetime para o início e fim do turno no dia atual
        inicio_turno = datetime(agora.year, agora.month, agora.day, hora_inicio, minuto_inicio)
        fim_turno = datetime(agora.year, agora.month, agora.day, hora_fim, minuto_fim)
        
        # Se o fim do turno for antes do início, significa que o turno passa para o dia seguinte
        if fim_turno < inicio_turno:
            fim_turno += timedelta(days=1)
            logger.info("Turno passa para o dia seguinte")
            
        # Se a hora atual for antes do início do turno, considerar o turno do dia anterior
        if agora < inicio_turno:
            inicio_turno -= timedelta(days=1)
            fim_turno -= timedelta(days=1)
            logger.info("Considerando turno do dia anterior")
            
        logger.info(f"Período do turno ajustado: {inicio_turno} até {fim_turno}")
        
        # Verificar se estamos dentro do turno
        if agora < inicio_turno or agora > fim_turno:
            logger.warning(f"Fora do horário de turno. Atual: {agora}, Turno: {inicio_turno} - {fim_turno}")
            return {
                'TempoRodando': 0,
                'TempoParado': 0,
                'Disponibilidade_Pct': 0.0
            }
            
        # Calcular o tempo decorrido do turno até agora (em segundos)
        tempo_decorrido = (agora - inicio_turno).total_seconds()
        logger.info(f"Tempo decorrido do turno: {tempo_decorrido/60:.2f} minutos")
        
        # Verificar paradas existentes
        cursor.execute("""
            SELECT IDParada, InicioParada, FimParada, Motivo
            FROM TBL_Paradas
            WHERE IDMaquina = ? AND 
                  ((InicioParada >= ? AND InicioParada <= ?) OR
                   (FimParada >= ? AND FimParada <= ?) OR
                   (InicioParada <= ? AND (FimParada >= ? OR FimParada IS NULL)))
            ORDER BY InicioParada DESC
        """, (id_maquina, inicio_turno, agora, inicio_turno, agora, inicio_turno, inicio_turno))
        
        paradas = cursor.fetchall()
        logger.info(f"Encontradas {len(paradas) if paradas else 0} paradas para a máquina no período")
        
        for p in paradas:
            logger.info(f"Parada ID: {p.IDParada}, Início: {p.InicioParada}, Fim: {p.FimParada}, Motivo: {p.Motivo}")
        
        # Obter os tempos de parada para a máquina no período do turno
        cursor.execute("""
            SELECT 
                SUM(DATEDIFF(SECOND, 
                    CASE 
                        WHEN InicioParada < ? THEN ? 
                        ELSE InicioParada 
                    END, 
                    CASE 
                        WHEN FimParada IS NULL THEN GETDATE() 
                        WHEN FimParada > ? THEN ?
                        ELSE FimParada 
                    END
                )) as TempoParadaTotal
            FROM TBL_Paradas
            WHERE IDMaquina = ? 
              AND (
                  (InicioParada >= ? AND InicioParada <= ?) OR
                  (FimParada >= ? AND FimParada <= ?) OR
                  (InicioParada <= ? AND (FimParada >= ? OR FimParada IS NULL))
              )
        """, (inicio_turno, inicio_turno, agora, agora, id_maquina, 
              inicio_turno, agora, inicio_turno, agora, inicio_turno, inicio_turno))
        
        resultado = cursor.fetchone()
        logger.info(f"Resultado da consulta de tempo parado: {resultado}")
        
        # Tratamento adequado para valores nulos
        if resultado and resultado[0] is not None:
            tempo_parado = float(resultado[0])
        else:
            tempo_parado = 0.0
        
        logger.info(f"Tempo parado calculado: {tempo_parado/60:.2f} minutos")
        
        # Garantir que o tempo parado não exceda o tempo decorrido
        tempo_parado = min(tempo_parado, tempo_decorrido)
        
        # Calcular o tempo rodando (tempo decorrido menos tempo parado)
        tempo_rodando = tempo_decorrido - tempo_parado
        logger.info(f"Tempo rodando calculado: {tempo_rodando/60:.2f} minutos")
        
        # Calcular a disponibilidade como porcentagem
        disponibilidade = (tempo_rodando / tempo_decorrido) * 100 if tempo_decorrido > 0 else 0.0
        logger.info(f"Disponibilidade calculada: {disponibilidade:.2f}%")
        
        return {
            'TempoRodando': round(tempo_rodando),
            'TempoParado': round(tempo_parado),
            'Disponibilidade_Pct': round(disponibilidade, 1)
        }
        
    except Exception as e:
        logger.error(f"Erro ao calcular disponibilidade: {e}")
        import traceback
        logger.error(traceback.format_exc())
        return {
            'TempoRodando': 0,
            'TempoParado': 0,
            'Disponibilidade_Pct': 0.0
        }     
        
if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000, debug=True, use_reloader=True)
