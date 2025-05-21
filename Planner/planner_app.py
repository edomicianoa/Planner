from flask import Flask, render_template, request, redirect, url_for, jsonify, session
import pyodbc
import json
from datetime import datetime
from functools import wraps
from datetime import timedelta


app = Flask(__name__)
app.secret_key = 'sua_chave_secreta_segura'

# Conexão com SQL Server Express
conn = pyodbc.connect(
    'DRIVER={ODBC Driver 17 for SQL Server};'
    'SERVER=Filipe\\SQLEXPRESS;'
    'DATABASE=PLN_PRD;'
    'Trusted_Connection=yes;'
)
cursor = conn.cursor()
cursor = conn.cursor()


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
                print(f"⚠️ Produção consolidada gravada por evento externo — chave: {chave}")
            except Exception as e:
                print("❌ Erro ao gravar consolidado:", e)

cursor = conn.cursor()
cursor = conn.cursor()

from collections import defaultdict
import threading

buffer_agregado = defaultdict(int)
lock = threading.Lock()

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
            print(f"🔄 Gravando {len(buffer_agregado)} registros consolidados no banco...")

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
                    print(f"❌ Erro ao gravar linha consolidada: {e}")

            conn.commit()
            buffer_agregado.clear()

# ----------------------------------------------
# FUNÇÃO CENTRAL PARA IDENTIFICAR O TURNO ATUAL
# ----------------------------------------------
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

    
def obter_disponibilidade_turno(id_maquina, id_turno=1):
    query = """
        SELECT TempoRodando, TempoParado, Disponibilidade_Pct
        FROM vw_DisponibilidadeTurnoAtual
        WHERE IDMaquina = ? AND IDTurno = ?
    """
    cursor.execute(query, (id_maquina, id_turno))
    row = cursor.fetchone()
    if row:
        return {
            'TempoRodando': row[0],
            'TempoParado': row[1],
            'Disponibilidade_Pct': round(row[2], 2)
        }
    else:
        return {
            'TempoRodando': 0,
            'TempoParado': 0,
            'Disponibilidade_Pct': 0
        }
  

# Decorador para proteger rotas
def login_requerido(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'usuario_id' not in session:
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function
    
      # Decorador para verificar permissões do grupo
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
        # Substitua pelo ID correto do grupo admin (por ex: 1)
        id_admin = 1  
        if session.get('usuario_grupo') != id_admin:
            return "Acesso restrito ao administrador.", 403
        return f(*args, **kwargs)
    return decorated_function
    

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
    
from flask import render_template, request, redirect, url_for, session
from functools import wraps

# Supondo que o cursor e conn já estão conectados ao seu banco

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
    
@app.route('/alterar_status_produto/<int:id_produto>/<int:status>')
def alterar_status_produto(id_produto, status):
    cursor = conn.cursor()
    cursor.execute("""
        UPDATE TBL_Produto
        SET Habilitado = ?
        WHERE IDProduto = ?
    """, (status, id_produto))
    conn.commit()
    cursor.close()

    return redirect(url_for('consulta_produtos'))

@app.route('/cadastro_recurso', methods=['GET', 'POST'])
def cadastro_recurso():
    id_edicao = request.args.get('id')
    recurso_editar = None

    if request.method == 'POST':
        nome = request.form['nome']
        codigo = request.form['codigo']
        tipo = request.form['tipo']
        ativo = 1 if 'ativo' in request.form else 0
        id_recurso = request.form.get('id_recurso')

        if id_recurso:
            cursor.execute("""
                UPDATE TBL_Recurso
                SET NomeMaquina = ?, CodigoInterno = ?, IDTipo = ?, Ativo = ?
                WHERE IDMaquina = ?
            """, nome, codigo, tipo, ativo, id_recurso)
        else:
            cursor.execute("""
                INSERT INTO TBL_Recurso (NomeMaquina, CodigoInterno, IDTipo, Ativo)
                VALUES (?, ?, ?, ?)
            """, nome, codigo, tipo, ativo)

        conn.commit()
        return redirect(url_for('cadastro_recurso'))

    if id_edicao:
        cursor.execute("SELECT * FROM TBL_Recurso WHERE IDMaquina = ?", id_edicao)
        recurso_editar = cursor.fetchone()

    cursor.execute("""
        SELECT R.*, T.NomeTipo
        FROM TBL_Recurso R
        LEFT JOIN TBL_TipoRecurso T ON R.IDTipo = T.IDTipo
    """)
    recursos = cursor.fetchall()

    cursor.execute("SELECT * FROM TBL_TipoRecurso")
    tipos = cursor.fetchall()

    return render_template(
        'cadastro_recurso.html',
        recurso_editar=recurso_editar,
        recursos=recursos,
        tipos=tipos
    )





@app.route('/status_maquina', methods=['POST'])
def status_maquina():
    data = request.json
    id_maquina = data['id_maquina']
    novo_status = data['status']  # 0 ou 1

    # Buscar último status
    cursor.execute("""
        SELECT TOP 1 IDStatus, Status, DataHoraInicio FROM TBL_StatusMaquina 
        WHERE IDMaquina = ? ORDER BY DataHoraInicio DESC
    """, (id_maquina,))
    row = cursor.fetchone()

    id_status_anterior = row[0] if row else None
    status_atual = row[1] if row else None

    # Verifica se existe status atual em aberto
    cursor.execute("""
        SELECT COUNT(*) FROM TBL_StatusMaquina 
        WHERE IDMaquina = ? AND DataHoraFim IS NULL
    """, (id_maquina,))
    em_aberto = cursor.fetchone()[0]

    if (status_atual is None) or (novo_status != status_atual) or (em_aberto == 0):
        # Fecha o anterior, se existir
        if row:
            cursor.execute("""
                UPDATE TBL_StatusMaquina 
                SET DataHoraFim = GETDATE() 
                WHERE IDMaquina = ? AND DataHoraFim IS NULL
            """, (id_maquina,))
            conn.commit()

            cursor.execute("""
                UPDATE TBL_StatusMaquina
                SET DiffStatusSegundos = DATEDIFF(SECOND, DataHoraInicio, DataHoraFim)
                WHERE IDStatus = ?
            """, (id_status_anterior,))
            conn.commit()

        # Buscar execução ativa
        cursor.execute("""
            SELECT TOP 1 E.IDExecucao, E.IDOrdem, R.IDTipo
            FROM TBL_ExecucaoOP E
            JOIN TBL_Recurso R ON R.IDMaquina = E.IDMaquina
            WHERE E.IDMaquina = ? AND E.DataHoraFim IS NULL AND E.Status = 'Em Execucao'
            ORDER BY E.IDExecucao DESC
        """, (id_maquina,))
        row_exec = cursor.fetchone()

        id_turno = None
        if row_exec:
            id_execucao, id_ordem, id_tipo_recurso = row_exec
            id_operador = 1
            agora = datetime.now().time()

            cursor.execute("""
                SELECT TOP 1 IDTurno FROM TBL_Turno
                WHERE ((HoraInicio <= ? AND HoraFim > ?) OR
                      (HoraInicio > HoraFim AND (HoraInicio <= ? OR HoraFim > ?)))
                      AND Ativo = 1
            """, (agora, agora, agora, agora))
            turno_result = cursor.fetchone()
            id_turno = turno_result[0] if turno_result else None

        # Grava novo status
        if novo_status == 0:
            cursor.execute("""
                INSERT INTO TBL_StatusMaquina 
                (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, IDMotivoParada, DescricaoStatus)
                VALUES (?, 0, GETDATE(), GETDATE(), ?, 11, 'Parada')
            """, (id_maquina, id_turno))
        else:
            cursor.execute("""
                INSERT INTO TBL_StatusMaquina 
                (IDMaquina, Status, DataHoraInicio, DataHoraRegistro, IDTurno, DescricaoStatus)
                VALUES (?, 1, GETDATE(), GETDATE(), ?, 'Producao')
            """, (id_maquina, id_turno))

        conn.commit()

    return jsonify({'mensagem': 'Status registrado com sucesso.'})



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
        

@app.route('/dashboard')
def dashboard():
    recursos = []

    cursor.execute("""
    SELECT IDMaquina, NomeMaquina, CodigoInterno, 
           ISNULL(MetaOEE, 90) AS MetaOEE, 
           ISNULL(MetaQualidade, 95) AS MetaQualidade, 
           ISNULL(MetaDisponibilidade, 92) AS MetaDisponibilidade, 
           ISNULL(MetaPerformance, 93) AS MetaPerformance
    FROM TBL_Recurso 
    WHERE Ativo = 1
    """)

    maquinas = cursor.fetchall()

    for maquina in maquinas:
        id_maquina = maquina.IDMaquina
        nome_maquina = maquina.NomeMaquina
        codigo_interno = maquina.CodigoInterno

        id_turno_atual = identificar_turno()
        print(f"🕒 ID do turno atual identificado: {id_turno_atual}")
        disponibilidade_dict = obter_disponibilidade_turno(id_maquina, id_turno_atual if id_turno_atual else 1)
        print(f"Disponibilidade retornada: {disponibilidade_dict}")

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
                    E.IDRecurso = ? 
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

            cursor.execute("SELECT HoraInicio FROM TBL_Turno WHERE IDTurno = ?", (id_turno_atual,))
            turno_info = cursor.fetchone()
            if turno_info:
                hora_inicio_turno = turno_info[0]
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

                print("=== DEBUG PERFORMANCE POR TURNO ===")
                print(f"ID Máquina: {id_maquina}")
                print(f"Turno Atual: {id_turno_atual}")
                print(f"Tempo Ciclo (s): {tempo_ciclo}")
                print(f"Fator: {fator}")
                print(f"Unidade: {sigla_unidade}")
                print(f"Velocidade Real (u/min): {velocidade_real}")
                print(f"Velocidade Planejada (u/min): {velocidade_planejada}")
                print(f"Performance Calculada: {performance}")

                            
        # --- Buscar status máquina
        cursor.execute("""
            SELECT TOP 1 Status, DataHoraInicio, IDMotivoParada FROM TBL_StatusMaquina 
            WHERE IDMaquina = ? AND DataHoraFim IS NULL 
            ORDER BY DataHoraInicio DESC
        """, id_maquina)
        row_status = cursor.fetchone()
        
        status_atual = row_status.Status if row_status else 0
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
            print("Erro ao calcular OEE:", e)
            oee = 0.0

        recurso = {
            'IDMaquina': id_maquina,
            'NomeMaquina': nome_maquina,
            'CodigoInterno': codigo_interno,
            'StatusAtual': status_atual,
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
            'DescricaoMotivoParada': descricao_motivo

        }
        
        print(f"Máquina {nome_maquina} | Ordem: {codigo_ordem} | Produzido: {quantidade_produzida} unidades | Tempo Ciclo: {tempo_ciclo} seg | Performance: {performance}% | Vel Planejada: {velocidade_planejada} u/min | Vel Real: {velocidade_real} u/min | Disponibilidade: {disponibilidade_pct}%")

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
        id_motivo_padrao=id_motivo_padrao
)

 
@app.route('/')
def index():
    return redirect(url_for('cadastro_produto'))

    
@app.route('/adicionar_op/<int:id_maquina>', methods=['GET', 'POST'])
def adicionar_op(id_maquina):
    from datetime import datetime

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
    id_maquina = request.form['id_maquina']

    # Buscar a execução atual
    cursor.execute("""
        SELECT TOP 1 IDExecucao, IDOrdem FROM TBL_ExecucaoOP
        WHERE IDMaquina = ? AND IDStatus = 5 AND DataHoraFim IS NULL
        ORDER BY IDExecucao DESC
    """, id_maquina)
    execucao = cursor.fetchone()

    if execucao:
        id_execucao, id_ordem = execucao
        cursor.execute("""
            UPDATE TBL_ExecucaoOP SET DataHoraFim = GETDATE(), IDStatus = 3
            WHERE IDExecucao = ?
        """, id_execucao)

        cursor.execute("""
            UPDATE TBL_OrdemProducao SET IDStatus = 3, IDStatus = 3 WHERE IDOrdem = ?
        """, id_ordem)

        cursor.execute("""
            INSERT INTO TBL_FilaOrdem (IDMaquina, IDOrdem, StatusFila)
            VALUES (?, ?, 'pendente')
        """, id_maquina, id_ordem)

        conn.commit()
        return jsonify({'status': 'ok'})

    return jsonify({'status': 'erro', 'mensagem': 'Nenhuma execução ativa encontrada.'})


@app.route('/finalizar_op', methods=['POST'])
def finalizar_op():
    id_maquina = request.form['id_maquina']

    cursor.execute("""
        SELECT TOP 1 IDExecucao, IDOrdem FROM TBL_ExecucaoOP
        WHERE IDMaquina = ? AND IDStatus = 5 AND DataHoraFim IS NULL
        ORDER BY IDExecucao DESC
    """, id_maquina)
    execucao = cursor.fetchone()

    if execucao:
        id_execucao, id_ordem = execucao
        cursor.execute("""
            UPDATE TBL_ExecucaoOP SET DataHoraFim = GETDATE(), IDStatus = 4
            WHERE IDExecucao = ?
        """, id_execucao)

        cursor.execute("""
            UPDATE TBL_OrdemProducao SET IDStatus = 4 WHERE IDOrdem = ?
        """, id_ordem)

        conn.commit()
        return jsonify({'status': 'ok'})

    return jsonify({'status': 'erro', 'mensagem': 'Nenhuma execução ativa encontrada.'})
    
@app.route('/fila_ordens/<int:id_maquina>', methods=['GET', 'POST'])
@app.route("/fila_ordens/<int:id_maquina>")
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
    
@app.route('/registrar_pulso', methods=['POST'])
def registrar_pulso():
    data = request.get_json()
    id_maquina = data.get('id_maquina')
    pulsos = int(data.get('pulsos', 1))

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

    cursor.execute("SELECT IDTipo FROM TBL_Recurso WHERE IDMaquina = ?", (id_maquina,))
    tipo_recurso_result = cursor.fetchone()
    id_tipo_recurso = tipo_recurso_result[0] if tipo_recurso_result else None

    # --- Operador fixo para manter a chave igual em todos os pontos
    id_operador = 1

    # --- Identificar turno atual
    agora = datetime.now().time()
    cursor.execute("""
        SELECT TOP 1 IDTurno 
        FROM TBL_Turno 
        WHERE 
            (HoraInicio <= ? AND HoraFim > ?) 
            OR 
            (HoraInicio > HoraFim AND (HoraInicio <= ? OR HoraFim > ?))
    """, (agora, agora, agora, agora))
    turno_result = cursor.fetchone()
    id_turno = turno_result[0] if turno_result else None

    quantidade = pulsos * fator

    chave = (
        id_execucao,
        id_maquina,
        id_tipo_recurso,
        id_ordem,
        id_turno,
        id_operador
    )

    with lock:
        if chave in buffer_agregado:
            buffer_agregado[chave]['quantidade'] += quantidade
        else:
            buffer_agregado[chave] = {
                'quantidade': quantidade,
                'hora_inicial': datetime.now()
        }

    return jsonify({"mensagem": "Pulso armazenado no buffer."})

 
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
    
@app.route('/registrar_refugo', methods=['POST'])
def registrar_refugo():
    data = request.get_json()
    id_maquina = data.get('id_maquina')
    id_motivo = data.get('id_motivo')
    quantidade = data.get('quantidade')
    id_operador = 1  # pode ajustar conforme o operador logado

    # Buscar execução ativa
    cursor.execute("""
        SELECT TOP 1 E.IDExecucao, E.IDOrdem, E.IDTurno, R.IDTipo
        FROM TBL_ExecucaoOP E
        JOIN TBL_Recurso R ON R.IDMaquina = E.IDMaquina
        WHERE E.IDMaquina = ? AND E.DataHoraFim IS NULL AND E.Status = 'Em Execucao'
        ORDER BY E.IDExecucao DESC
    """, (id_maquina,))
    execucao = cursor.fetchone()

    if not execucao:
        return jsonify({"status": "erro", "mensagem": "Nenhuma execução ativa encontrada."}), 404

    id_execucao, id_ordem, id_turno, id_tipo_recurso = execucao

    # ⚠️ FORÇA gravação consolidada da produção ANTES do evento de refugo
    chave = (id_execucao, id_maquina, id_tipo_recurso, id_ordem, id_turno, id_operador)
    print(f"📦 Consolidando produção antes do REFUGO | Chave: {chave}")
    forcar_gravacao_consolidada(chave)

    # Inserir evento de refugo com todos os campos completos
    cursor.execute("""
        INSERT INTO TBL_EventoProducao (
            IDExecucao, IDTipoEvento, Quantidade, DataHoraEvento,
            IDRecurso, IDTipoRecurso, IDOrdemProducao, IDTurno,
            IDOperador, TipoValor, ObsEvento, IDStatus, IDMotivoRefugo, OrigemEvento
        )
        VALUES (?, 2, ?, GETDATE(), ?, ?, ?, ?, ?, 'REFUGO', ?, ?, ?, 'MANUAL')
    """, (
        id_execucao, quantidade, id_maquina, id_tipo_recurso,
        id_ordem, id_turno, id_operador,
        None,     # ObsEvento deve ser NULL
        5,        # IDStatus padrão
        id_motivo
    ))

    conn.commit()
    return jsonify({"mensagem": "Refugo registrado com sucesso."})

    
@app.route('/registrar_parada', methods=['POST'])
def registrar_parada():
    from datetime import datetime

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
    if request.method == 'POST':
        nome = request.form['nome']
        codigo = request.form['codigo']
        descricao = request.form['descricao']
        ativo = 1 if 'ativo' in request.form else 0
        id_empresa = request.form['id_empresa']
        id_area = request.form['id_area']

        cursor.execute("""
            INSERT INTO TBL_Setor (Nome, Codigo, Descricao, Ativo, DtCriacao, IDEmpresa, IDArea)
            VALUES (?, ?, ?, ?, GETDATE(), ?, ?)
        """, (nome, codigo, descricao, ativo, id_empresa, id_area))
        conn.commit()

    cursor.execute("SELECT IDSetor, Nome, Codigo, Descricao, Ativo, IDEmpresa, IDArea FROM TBL_Setor")
    setores = cursor.fetchall()

    cursor.execute("SELECT IDEmpresa, Nome FROM TBL_Empresa")
    empresas = cursor.fetchall()

    cursor.execute("SELECT IDArea, Nome FROM TBL_Area")
    areas = cursor.fetchall()

    return render_template('cadastro_setor.html', setores=setores, empresas=empresas, areas=areas)


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







@app.route('/cadastro_grupo_alarme')
def cadastro_grupo_alarme():
    return render_template('cadastro_grupo_alarme.html')

@app.route('/cadastro_motivo_alarme')
def cadastro_motivo_alarme():
    return render_template('cadastro_motivo_alarme.html')

@app.route('/cadastro_ferramenta')
def cadastro_ferramenta():
    return render_template('cadastro_ferramenta.html')

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



from datetime import datetime, timedelta

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
        JOIN TBL_Produto P ON P.IDProduto = O.IDProduto
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





from datetime import datetime, timedelta

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





if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000, debug=True, use_reloader=True)


##if __name__ == '__main__':
    ##app.run(host='192.168.15.4', port=5000, debug=False, use_reloader=True)

