import marimo

__generated_with = "0.25.1"
app = marimo.App(width="medium")


@app.cell
def _():
    import marimo as mo

    return (mo,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # Exercício 1 — Game of Life como Máquina de Estados Finita

    Neste trabalho modela-se uma variante do Conway's Game of Life, com espaço de estados finito, como uma máquina de estados finita (FSM). A FSM é codificada em lógica com o pySMT (solver Z3).

    Depois verificam-se duas propriedades com Bounded Model Checking (BMC):

    1. nunca se alcança o estado de erro;
    2. nenhuma célula normal está permanentemente morta ou permanentemente viva.
    """)
    return


@app.cell
def _():
    import random
    from pysmt.shortcuts import (Symbol, Bool, Int, And, Or, Not, Iff, Implies,
                                 Ite, Equals, Plus, ExactlyOne, Solver)
    from pysmt.typing import BOOL

    return (
        And,
        BOOL,
        Bool,
        Equals,
        ExactlyOne,
        Iff,
        Implies,
        Int,
        Ite,
        Not,
        Or,
        Plus,
        Solver,
        Symbol,
        random,
    )


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 1. Parâmetros

    - N — dimensão da grelha de células normais. O enunciado exige N > 16, por isso usamos N = 17.
    - MODO — escolhe a relação de transição da FSM:
        - "assincrono" (alínea a.i): em cada transição, uma e só uma célula normal muda de estado;
        - "sincrono" (alínea a.ii): em cada transição, todas as células normais transitam em simultâneo.
    - K — número máximo de transições exploradas pelo BMC.
    - SEMENTE — semente usada para sortear as células iniciais na simulação.

    Ao mudar o valor de MODO, o marimo volta a correr automaticamente todas as células que dependem dele.
    """)
    return


@app.cell
def _():
    N = 17
    MODO = "sincrono"     # "sincrono" (a.ii) ou "assincrono" (a.i)
    K = 15                # número máximo de transições exploradas pelo BMC
    SEMENTE = 2026        # semente para sortear as células iniciais na simulacão

    assert N > 16
    assert MODO in ("sincrono", "assincrono")
    return K, MODO, N, SEMENTE


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 2. Organização da grelha

    Usamos índices (i,j) $\in$ \{0,...,N+1\}^2, ou seja, uma grelha de (N+2) x (N+2) com três tipos de células:

    | Tipo | Condição | Quantidade | Comportamento |
    |---|---|---|---|
    | normais | 1 <= i,j <= N | N^2 | evoluem segundo a regra B3/S23 |
    | iniciais | min(i,j)=0 e max(i,j) <= N | 2N+1 | constantes, sorteadas no estado inicial |
    | finais | max(i,j)=N+1 | 2N+3 | sempre mortas |

    As celulas (i_0,j_0) e (i_1,j_1) são vizinhas sse max(|i_0-i_1|,|j_0-j_1|)=1, ou seja, cada celula tem como vizinhas as 8 células à sua volta.

    Uma celula normal tem sempre os seus 8 vizinhos dentro desta grelha alargada, por isso não há casos especiais nas bordas. Os assert confirmam as quantidades dadas no enunciado.
    """)
    return


@app.cell
def _(N):
    NORMAIS = [(i, j) for i in range(1, N + 1) for j in range(1, N + 1)]
    INICIAIS = [(i, j) for i in range(N + 1) for j in range(N + 1) if min(i, j) == 0]
    FINAIS = [(i, j) for i in range(N + 2) for j in range(N + 2) if max(i, j) == N + 1]

    assert len(NORMAIS) == N * N
    assert len(INICIAIS) == 2 * N + 1
    assert len(FINAIS) == 2 * N + 3


    def vizinhos(i, j):
        return [(i + di, j + dj)
                for di in (-1, 0, 1) for dj in (-1, 0, 1)
                if (di, dj) != (0, 0)]

    return FINAIS, INICIAIS, NORMAIS, vizinhos


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 3. Estado da FSM — declare

    Cada estado s_k de um traço é um dicionário que associa a cada célula uma fórmula booleana (True = viva, False = morta):

    - célula normal ou inicial -> uma variável c_i_j_k;
    - célula final -> a constante False, que não precisa de variável porque nunca muda.

    As células iniciais fazem parte do estado (têm uma variável em cada s_k), mas a relação de transição obriga-as a manter o seu valor.
    """)
    return


@app.cell
def _(BOOL, Bool, FINAIS, INICIAIS, NORMAIS, Symbol):
    def declare(k):
        s = {}
        for (i, j) in NORMAIS + INICIAIS:
            s[(i, j)] = Symbol(f"c_{i}_{j}_{k}", BOOL)
        for (i, j) in FINAIS:
            s[(i, j)] = Bool(False)
        return s

    return (declare,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 4. Estado inicial — init

    $$init(s) \;\equiv\; \bigwedge_{1\le i,j\le 3} s_{i,j} \;\;\wedge \bigwedge_{(i,j)\ \text{normal},\ \max(i,j)>3} \neg\, s_{i,j}$$

    As células iniciais não são restringidas. Ficam livres, e o solver pode escolher qualquer combinação de valores.

    Isto modela o sorteio aleatório. Cada célula inicial está viva com probabilidade 1/2, por isso todas as 2^{2N+1} configurações possíveis têm probabilidade positiva. Uma propriedade só é válida se for válida para todas elas.

    Para a simulação, fronteira_aleatoria fixa um sorteio concreto, gerado com a semente SEMENTE.
    """)
    return


@app.cell
def _(And, INICIAIS, NORMAIS, Not, random):
    def init(s):
        return And([s[(i, j)] if (i <= 3 and j <= 3) else Not(s[(i, j)])
                    for (i, j) in NORMAIS])


    def fronteira_aleatoria(s, semente):
        rng = random.Random(semente)
        return And([s[c] if rng.random() < 0.5 else Not(s[c]) for c in INICIAIS])

    return fronteira_aleatoria, init


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 5. Regra B3/S23

    Seja n o número de vizinhos vivos da célula (i,j) no estado s. O valor seguinte da célula é:

    $$regra(s,i,j) \;\equiv\; (n = 3) \;\vee\; (s_{i,j} \wedge n = 2)$$

    - nasce se está morta e tem n=3;
    - sobrevive se está viva e tem n $\in$ {2,3};
    - caso contrário, morre ou continua morta.

    O n é calculado em aritmética inteira, somando Ite(viva, 1, 0) para cada vizinho.
    """)
    return


@app.cell
def _(And, Equals, Int, Ite, Or, Plus, vizinhos):
    def num_vivos(s, i, j):
        return Plus([Ite(s[v], Int(1), Int(0)) for v in vizinhos(i, j)])


    def regra(s, i, j):
        n = num_vivos(s, i, j)
        return Or(Equals(n, Int(3)), And(s[(i, j)], Equals(n, Int(2))))

    return (regra,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 6. Relação de transição — trans

    Em ambos os modos, as células iniciais mantêm o seu valor. As células finais são constantes por construção.

    Modo síncrono (a.ii) — todas as células normais atualizam ao mesmo tempo:

    $$\bigwedge_{(i,j)\ \text{normal}} \big(s'_{i,j} \leftrightarrow regra(s,i,j)\big)$$

    Modo assíncrono (a.i) — uma e so uma celula normal muda, e essa mudança respeita a regra:

    $$ExactlyOne_{(i,j)}\big(s'_{i,j} \neq s_{i,j}\big) \;\wedge\; \bigwedge_{(i,j)} \big(s'_{i,j}\neq s_{i,j} \rightarrow (s'_{i,j} \leftrightarrow regra(s,i,j))\big)$$

    Decisão de modelação: estados estáveis. Um estado é estável quando todas as células já satisfazem a regra. Nesse caso nenhuma célula pode mudar, e no modo assíncrono não haveria nenhuma transição possível (deadlock).

    Para que todas as execuções sejam infinitas, permitimos que o sistema fique no mesmo estado, mas apenas nos estados estáveis. No modo síncrono isto acontece naturalmente, porque um estado estável transita para si próprio.

    A função trans escolhe a relação de transição conforme o valor do parâmetro MODO.
    """)
    return


@app.cell
def _(And, ExactlyOne, INICIAIS, Iff, Implies, MODO, NORMAIS, Not, Or, regra):
    def mantem(s, p, celulas):
        return And([Iff(p[c], s[c]) for c in celulas])


    def estavel(s):
        return And([Iff(s[c], regra(s, *c)) for c in NORMAIS])


    def trans_sincrona(s, p):
        return And(mantem(s, p, INICIAIS),
                   And([Iff(p[c], regra(s, *c)) for c in NORMAIS]))


    def trans_assincrona(s, p):
        muda = {c: Not(Iff(p[c], s[c])) for c in NORMAIS}
        uma_celula = And(ExactlyOne(list(muda.values())),
                         And([Implies(muda[c], Iff(p[c], regra(s, *c))) for c in NORMAIS]))
        fica = And(estavel(s), mantem(s, p, NORMAIS))
        return And(mantem(s, p, INICIAIS), Or(uma_celula, fica))


    def trans(s, p):
        if MODO == "sincrono":
            return trans_sincrona(s, p)
        return trans_assincrona(s, p)

    return (trans,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 7. Visualização e simulação

    Para visualizar os traços, desenhamos a grelha de (N+2) x(N+2) em texto:

    | Símbolo | Significado |
    |---|---|
    | # / . | célula normal viva / morta |
    | o / - | célula inicial viva / morta |
    | x | célula final (sempre morta) |

    - gera_traco(k, extra) pede ao solver um traço com k transições a partir do estado inicial. O argumento extra é uma condição opcional sobre s_0, como o sorteio das células iniciais.
    - mostra_traco desenha os estados lado a lado.
    """)
    return


@app.cell
def _(INICIAIS, N, NORMAIS, Solver, declare, init, mo, trans):
    def extrai(sol, traco):
        return [{c: sol.get_py_value(s[c]) for c in NORMAIS + INICIAIS} for s in traco]


    def desenha(valores):
        linhas = []
        for i in range(N + 2):
            linha = ""
            for j in range(N + 2):
                if max(i, j) == N + 1:
                    linha += "x"
                elif min(i, j) == 0:
                    linha += "o" if valores[(i, j)] else "-"
                else:
                    linha += "#" if valores[(i, j)] else "."
            linhas.append(linha)
        return "\n".join(linhas)


    def mostra_traco(estados, titulo=""):
        caixas = [mo.md(f"**s{k}**\n```\n{desenha(v)}\n```") for k, v in enumerate(estados)]
        return mo.vstack([mo.md(titulo), mo.hstack(caixas, wrap=True, justify="start")])


    def gera_traco(k, extra=None):
        with Solver(name="z3") as sol:
            traco = [declare(t) for t in range(k + 1)]
            sol.add_assertion(init(traco[0]))
            if extra is not None:
                sol.add_assertion(extra(traco[0]))
            for t in range(k):
                sol.add_assertion(trans(traco[t], traco[t + 1]))
            if sol.solve():
                return extrai(sol, traco)
            return None

    return extrai, gera_traco, mostra_traco


@app.cell
def _(MODO, SEMENTE, fronteira_aleatoria, gera_traco, mostra_traco):
    _estados = gera_traco(6, lambda s: fronteira_aleatoria(s, SEMENTE))
    mostra_traco(_estados, f"Simulação ({MODO}) com as celulas iniciais sorteadas (semente {SEMENTE})")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 8. Propriedade b.i — "Nunca se alcança o estado de erro"

    O estado de erro é aquele em que todas as células normais estão mortas:

    $$erro(s) \;\equiv\; \bigwedge_{(i,j)\ \text{normal}} \neg\, s_{i,j}$$

    A propriedade é o invariante $\mathbf{G}\,\neg erro$. Para a verificar usamos BMC: para k = 0, 1, ... , K, perguntamos ao solver se existe um traço $s_0 \to s_1 \to \dots \to s_k$ com init(s_0) e erro(s_k).

    - Se existir, esse traço é um contra-exemplo e a propriedade é falsa.
    - Se não existir até K, só sabemos que não há erro nos primeiros K passos. Para provar a propriedade seria preciso, por exemplo, k-indução.

    A implementação é incremental. O mesmo solver vai acumulando as transições, e a condição erro(s_k) é passada como *assumption*, ficando ativa apenas nessa chamada. Assim, o primeiro $k$ encontrado é o contra-exemplo mais curto.
    """)
    return


@app.cell
def _(And, NORMAIS, Not, Solver, declare, extrai, init, trans):
    def erro(s):
        return And([Not(s[c]) for c in NORMAIS])


    def bmc_always(inv, K):
        with Solver(name="z3") as sol:
            traco = [declare(0)]
            sol.add_assertion(init(traco[0]))
            for k in range(K + 1):
                if sol.solve([Not(inv(traco[k]))]):
                    return k, extrai(sol, traco)
                traco.append(declare(k + 1))
                sol.add_assertion(trans(traco[k], traco[k + 1]))
            return None, None

    return bmc_always, erro


@app.cell
def _(K, MODO, Not, bmc_always, erro, mo, mostra_traco):
    _k, _estados = bmc_always(lambda s: Not(erro(s)), K)
    if _k is None:
        _res = mo.md(f"Não foi encontrado nenhum contra-exemplo até {K} transições ({MODO}).")
    else:
        _res = mostra_traco(_estados, f"Contra-exemplo ({MODO}): o estado de erro é alcançado ao fim de {_k} transições.")
    _res
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### Discussão de b.i

    A propriedade é falsa nos dois modos:

    - Síncrono: existe uma configuração das células iniciais para a qual todas as células normais morrem ao fim de 3 transições.
    - Assíncrono: o erro é alcançado ao fim de 9 transições. Este é o mínimo possível: há 9 células vivas no início e, em cada transição, só uma célula muda, por isso são precisas pelo menos 9 mortes.

    Como o BMC encontrou contra-exemplos, não é necessário tentar uma prova por k-indução.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 9. Propriedade b.ii — "Nenhuma célula normal está permanentemente morta ou permanentemente viva"

    Interpretação. Numa execução (infinita), uma célula $c$ está:

    - permanentemente morta se está morta em todos os estados ($\mathbf{G}\,\neg c$);
    - permanentemente viva se está viva em todos os estados ($\mathbf{G}\,c$).

    A propriedade afirma que nenhuma execução tem uma célula assim. Para a refutar, basta encontrar uma execução e uma célula com valor constante.

    Contra-exemplos em laço (lasso). Como o espaço de estados é finito, qualquer execução infinita acaba por repetir um estado. Por isso, um contra-exemplo pode ser apresentado como um traço finito que volta a um estado anterior:

    $$init(s_0) \;\wedge\; \bigwedge_{t<k} trans(s_t,s_{t+1}) \;\wedge\; \bigvee_{l<k} (s_k = s_l) \;\wedge\; \bigwedge_{t\le k} (s_t)_c = v$$

    O traço infinito $s_0 ... s_{l-1}\,(s_l ... s_{k-1})^\omega$ é uma execução válida em que a célula c tem sempre o valor v. Procuramos estes laços com BMC, aumentando k até K.

    Um contra-exemplo para a leitura "sempre" ($\mathbf{G}$) é também um contra-exemplo para a leitura mais fraca "a partir de certo momento" ($\mathbf{F}\mathbf{G}$). Por isso, os resultados valem para as duas interpretações.
    """)
    return


@app.cell
def _(
    And,
    INICIAIS,
    Iff,
    K,
    MODO,
    NORMAIS,
    Not,
    Or,
    Solver,
    declare,
    extrai,
    init,
    mo,
    mostra_traco,
    trans,
):
    def iguais(a, b):
        return And([Iff(a[c], b[c]) for c in NORMAIS + INICIAIS])


    def bmc_laco_permanente(celula, viva, K):
        def valor(s):
            return s[celula] if viva else Not(s[celula])

        with Solver(name="z3") as sol:
            traco = [declare(0)]
            sol.add_assertion(init(traco[0]))
            sol.add_assertion(valor(traco[0]))
            for k in range(1, K + 1):
                traco.append(declare(k))
                sol.add_assertion(trans(traco[k - 1], traco[k]))
                sol.add_assertion(valor(traco[k]))
                fecha_laco = Or([iguais(traco[k], traco[l]) for l in range(k)])
                if sol.solve([fecha_laco]):
                    estados = extrai(sol, traco)
                    l = next(l for l in range(k) if estados[l] == estados[k])
                    return k, l, estados
            return None, None, None


    def relatorio_laco(celula, viva):
        k, l, estados = bmc_laco_permanente(celula, viva, K)
        estado_txt = "viva" if viva else "morta"
        if k is None:
            return mo.md(f"Não foi encontrado nenhum laço até {K} transições com a célula {celula} sempre {estado_txt} ({MODO}).")
        if k - l == 1:
            laco_txt = f"s{l} transita para si próprio, por isso o sistema fica nesse estado para sempre."
        else:
            laco_txt = f"Como s{k} = s{l}, o traço repete s{l}…s{k-1} para sempre."
        return mostra_traco(estados,
            f"Contra-exemplo ({MODO}): a célula {celula} está sempre {estado_txt}. {laco_txt}")

    return (relatorio_laco,)


@app.cell
def _(N, relatorio_laco):
    relatorio_laco((N, N), viva=False)
    return


@app.cell
def _(relatorio_laco):
    relatorio_laco((3, 3), viva=True)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### Discussão de b.ii

    A propriedade é falsa nos dois modos:

    - Permanentemente morta: a célula (N,N), no canto oposto ao bloco inicial, nunca chega a nascer. Por exemplo, a atividade pode extinguir-se ou estabilizar perto do canto (1,1) antes de lá chegar.
    - Permanentemente viva: a célula (3,3), que começa viva, pode manter-se viva para sempre numa configuração que estabiliza.

    No modo assíncrono, os laços terminam num estado estável (o sistema fica parado nesse estado, como decidido na secção 6).
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 10. Conclusões

    | Propriedade | Modo síncrono | Modo assíncrono |
    |---|---|---|
    | b.i — nunca se alcança o erro | Falsa (erro em 3 transições) | Falsa (erro em 9 transições) |
    | b.ii — nenhuma célula sempre morta | Falsa (célula (N,N)) | Falsa (célula (N,N)) |
    | b.ii — nenhuma célula sempre viva | Falsa (célula (3,3)) | Falsa (célula (3,3)) |

    - Todas as propriedades foram refutadas com contra-exemplos concretos obtidos por BMC. Por isso, nenhuma delas precisa de uma prova por indução.
    - O facto de as células iniciais serem sorteadas é essencial. O solver escolhe a configuração da fronteira, e qualquer configuração é possível, com probabilidade 2^{-(2N+1)}.
    - Para reproduzir os resultados do outro modo, basta alterar o parâmetro MODO na secção 1.

    Para a realização deste trabalho, foi utilizada a ferramenta de Inteligência Artificial Gemini como apoio na resolução de dúvidas, no desenvolvimento do código e formatação de texto.

    Link: https://share.gemini.google/cxfcjnSXBLSh
    """)
    return


if __name__ == "__main__":
    app.run()
