import marimo

__generated_with = "0.25.0"
app = marimo.App()


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    #TP2.3

    ##Grupo 19
    João Pontes, A111657

    João Paulo, A110393

    Objetivo:
        1. Construir um SFOTS, usando BitVec’s de tamanho n , que descreva o comportamento de um CFA (Control Flow Automaton);
        2. Usando k-indução verificar, nesse SFOTS, se a propriedade (x*y + z = a*b) é um invariante do seu comportamento.
        3. Usando k-indução no SFOTS acima e adicionando ao estado inicial a condição (a < 2^{n/2}) ∧ (b < 2^{n/2}), verificar a segurança do programa;
        4. Codificar a propriedade de animação que exprime que o programa termina quaisquer que sejam os valores iniciais de a e b

    ---
    """)
    return


@app.cell
def _():
    #init dos nodos do CFA
    import marimo as mo
    from z3 import(
        BitVec, BitVecs, BitVecVal, Const, EnumSort, Solver,
        And, Or, Not, If, simplify, sat, unsat,
        ULT, ULE, UGT, UGE, UDiv, LShR, substitute, ZeroExt, Extract
    )


    n_init = BitVecVal(1,3)
    n_skip = BitVecVal(2,3)
    n_left = BitVecVal(3,3)
    n_right = BitVecVal(4,3)
    n_stop = BitVecVal(5,3)
    n_error = BitVecVal(6,3)

    pc = BitVec('pc', 3)

    dom_pc = And(ULE(1,pc), UGE(6,pc))

    for k in range(8):
        print(k, simplify(substitute(dom_pc, (pc, BitVecVal(k, 3)))))

    s = Solver()
    s.add(dom_pc)
    print(s.check())


    return (
        And,
        BitVec,
        BitVecs,
        Extract,
        Not,
        Or,
        Solver,
        UDiv,
        ZeroExt,
        dom_pc,
        mo,
        n_error,
        n_init,
        n_left,
        n_right,
        n_skip,
        n_stop,
        pc,
        sat,
    )


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Variáveis Globais & Overflow check**

    ---
    """)
    return


@app.cell
def _(BitVec, BitVecs, Extract, ZeroExt):
    #n-bits
    n = 8

    #declaração de x,y,z
    x, y, z = BitVecs('x y z', n)

    a, b = BitVecs('a b', n)
    a_, b_ = BitVecs('a_ b_', n)
    x_, y_, z_ = BitVecs('x_ y_ z_', n)
    pc_ = BitVec('pc_', 3)

    def ovfl_add(u, v):
        n_bits = u.size()
        sum  = ZeroExt(1, u) + ZeroExt(1,v)
        return Extract(n_bits, n_bits, sum) == 1
    #def ovfl_dbl(u, v):
    
    return a, a_, b, b_, n, ovfl_add, pc_, x, x_, y, y_, z, z_


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Estado Inicial**

    ---
    """)
    return


@app.cell
def _(And, Not, Solver, a, b, dom_pc, n_skip, pc, x, y, z):
    def initcfa(pc, x, y, z, a, b): #init ja no skip
        return And(pc == n_skip, x == a, y == b, z == 0) #colocamos pc em skip, assim definimos x, y e z

    inits = Solver()
    inits.add(dom_pc)
    inits.add(initcfa(pc, x, y, z, a, b))
    print(inits.check()) # sat neste caso

    for name, neg in [
        ("pc", Not(pc == n_skip)),
        ("x",  Not(x == a)),
        ("y",  Not(y == b)),
        ("z",  Not(z == 0)),
    ]:
        inits.push()
        inits.add(neg)
        print(name, inits.check()) # unsat em todos os restantes
        inits.pop()

    print(inits.assertions()) # só dom_pc e initcf




    return (initcfa,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Skip -> Stop**

    ---
    """)
    return


@app.cell
def _(
    And,
    Not,
    Solver,
    a,
    a_,
    b,
    b_,
    dom_pc,
    n_skip,
    n_stop,
    pc,
    pc_,
    x,
    x_,
    y,
    y_,
    z,
    z_,
):
    def skiptostop(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_):
        return And(pc == n_skip, pc_ == n_stop, y == 0, x_ == x, y_ == y, z == z_, a_ == a, b_ == b)


    stss = Solver()
    stss.add(dom_pc)
    stss.add(skiptostop(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_))
    print(stss.check()) # sat neste caso

    for name1, neg1 in [
        ("pc_", Not(pc_ == n_stop)),
        ("x_",  Not(x_ == x)),
        ("y_",  Not(y_ == y)),
        ("y",   Not(y == 0)),
        ("z_",  Not(z_ == z)),
        ("a_",  Not(a_ == a)),
        ("b_",  Not(b_ == b))   
    ]:
        stss.push()
        stss.add(neg1)
        print(name1, stss.check()) # unsat em todos os restantes
        stss.pop()

    print(stss.assertions()) 

    
    return (skiptostop,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Skip -> Left**

    ---
    """)
    return


@app.cell
def _(
    And,
    Not,
    Solver,
    a,
    a_,
    b,
    b_,
    dom_pc,
    n_left,
    n_skip,
    pc,
    pc_,
    x,
    x_,
    y,
    y_,
    z,
    z_,
):
    def skiptoleft(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_):
        return And(pc == n_skip, pc_ == n_left, x_ == x, y_ == y, z_ == z, a_ == a, b_ == b, (y & 1) == 0, y != 0)


    stls = Solver()
    stls.add(dom_pc)
    stls.add(skiptoleft(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_))
    print(stls.check()) # sat neste caso

    for name2, neg2 in [
        ("pc",  Not(pc == n_skip)),
        ("pc_", Not(pc_ == n_left)),
        ("x_",  Not(x_ == x)),
        ("y_",  Not(y_ == y)),
        ("y",   Not(y != 0)),
        ("y",   Not((y & 1) == 0)),
        ("z_",  Not(z_ == z)),
        ("a_",  Not(a_ == a)),
        ("b_",  Not(b_ == b))   
    ]:
        stls.push()
        stls.add(neg2)
        print(name2, stls.check()) # unsat em todos os restantes
        stls.pop()

    print(stls.assertions()) 
    return (skiptoleft,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Skip -> Right**

    ---
    """)
    return


@app.cell
def _(
    And,
    Not,
    Solver,
    a,
    a_,
    b,
    b_,
    dom_pc,
    n_right,
    n_skip,
    pc,
    pc_,
    x,
    x_,
    y,
    y_,
    z,
    z_,
):
    def skiptoright(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_):
        return And(pc == n_skip, pc_ == n_right, x_ == x, y_ == y, z_ == z, a_ == a, b_ == b, (y & 1) != 0, y != 0)

    strs = Solver()
    strs.add(dom_pc)
    strs.add(skiptoright(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_))
    print(strs.check()) # sat neste caso

    for name3, neg3 in [
        ("pc",  Not(pc == n_skip)),
        ("pc_", Not(pc_ == n_right)),
        ("x_",  Not(x_ == x)),
        ("y_",  Not(y_ == y)),
        ("y",   Not(y != 0)),
        ("y",   Not((y & 1) != 0)),
        ("z_",  Not(z_ == z)),
        ("a_",  Not(a_ == a)),
        ("b_",  Not(b_ == b))   
    ]:
        strs.push()
        strs.add(neg3)
        print(name3, strs.check()) # unsat em todos os restantes
        strs.pop()

    print(strs.assertions()) 
    return (skiptoright,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Left -> Skip**

    ---
    """)
    return


@app.cell
def _(
    And,
    Not,
    Solver,
    UDiv,
    a,
    a_,
    b,
    b_,
    dom_pc,
    n_left,
    n_skip,
    ovfl_add,
    pc,
    pc_,
    x,
    x_,
    y,
    y_,
    z,
    z_,
):
    def lefttoskip(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_):
        return And(pc == n_left, pc_ == n_skip, Not(ovfl_add(x,x)), x_ == 2 * x, y_ == UDiv(y, 2), z_ == z, a_ == a, b_ == b) # adicionar overflow check aqui


    ltss= Solver()
    ltss.add(dom_pc)
    ltss.add(lefttoskip(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_))
    print(ltss.check()) # sat neste caso

    for name4, neg4 in [
        ("pc",  Not(pc == n_left)),
        ("pc_", Not(pc_ == n_skip)),
        ("x_",  Not(x_ == 2 * x)),
        ("y_",  Not(y_ == UDiv(y, 2))),
        ("z_",  Not(z_ == z)),
        ("a_",  Not(a_ == a)),
        ("b_",  Not(b_ == b))   
    ]:
        ltss.push()
        ltss.add(neg4)
        print(name4, ltss.check()) # unsat em todos os restantes
        ltss.pop()

    print(ltss.assertions()) 
    return (lefttoskip,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Right -> Skip**

    ---
    """)
    return


@app.cell
def _(
    And,
    Not,
    Solver,
    a,
    a_,
    b,
    b_,
    dom_pc,
    n_right,
    n_skip,
    ovfl_add,
    pc,
    pc_,
    x,
    x_,
    y,
    y_,
    z,
    z_,
):
    def righttoskip(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_):
        return And(Not(ovfl_add(z,x)), pc == n_right, pc_ == n_skip, x_ == x, y_ == y - 1, z_ == z + x, a_ == a, b_ == b)



    rtss = Solver()
    rtss.add(dom_pc)
    rtss.add(righttoskip(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_))
    print(rtss.check()) # sat neste caso

    for name5, neg5 in [
        ("pc",  Not(pc == n_right)),
        ("pc_", Not(pc_ == n_skip)),
        ("x_",  Not(x_ == x)),
        ("y_",  Not(y_ == y - 1)),
        ("z_",  Not(z_ == z + x)),
        ("a_",  Not(a_ == a)),
        ("b_",  Not(b_ == b))   
    ]:
        rtss.push()
        rtss.add(neg5)
        print(name5, rtss.check()) # unsat em todos os restantes
        rtss.pop()

    print(rtss.assertions()) 

    return (righttoskip,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Left -> Error**

    ___
    """)
    return


@app.cell
def _(
    And,
    Not,
    Solver,
    a,
    a_,
    b,
    b_,
    dom_pc,
    n_error,
    n_left,
    ovfl_add,
    pc,
    pc_,
    x,
    x_,
    y,
    y_,
    z,
    z_,
):
    def lefttoerror(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_):
        return And(pc == n_left, pc_ == n_error, ovfl_add(x, x), x_ == x, y_ == y, z_ == z, a_ == a, b_ == b)

    ltes = Solver()
    ltes.add(dom_pc)
    ltes.add(lefttoerror(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_))
    print(ltes.check()) # sat neste caso

    for name6, neg6 in [
        ("pc",  Not(pc == n_left)),
        ("pc_", Not(pc_ == n_error)),
        ("x_",  Not(x_ == x)),
        ("ovfl",Not(ovfl_add(x,x))),
        ("y_",  Not(y_ == y)),
        ("z_",  Not(z_ == z)),
        ("a_",  Not(a_ == a)),
        ("b_",  Not(b_ == b))   
    ]:
        ltes.push()
        ltes.add(neg6)
        print(name6, ltes.check()) # unsat em todos os restantes
        ltes.pop()

    print(ltes.assertions()) 

    return (lefttoerror,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Right -> Error**

    ---
    """)
    return


@app.cell
def _(
    And,
    Not,
    Solver,
    a,
    a_,
    b,
    b_,
    dom_pc,
    n_error,
    n_right,
    ovfl_add,
    pc,
    pc_,
    x,
    x_,
    y,
    y_,
    z,
    z_,
):
    def righttoerror(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_):
        return And(pc == n_right, pc_ == n_error, ovfl_add(z, x), x_ == x, y_ == y, z_ == z, a_ == a, b_ == b)


    rtes = Solver()
    rtes.add(dom_pc)
    rtes.add(righttoerror(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_))
    print(rtes.check()) # sat neste caso

    for name7, neg7 in [
        ("pc",  Not(pc == n_right)),
        ("pc_", Not(pc_ == n_error)),
        ("ovfl",Not(ovfl_add(z,x))),
        ("x_",  Not(x_ == x)),
        ("y_",  Not(y_ == y)),
        ("z_",  Not(z_ == z)),
        ("a_",  Not(a_ == a)),
        ("b_",  Not(b_ == b))   
    ]:
        rtes.push()
        rtes.add(neg7)
        print(name7, rtes.check()) # unsat em todos os restantes
        rtes.pop()

    print(rtes.assertions()) 
    return (righttoerror,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Teste Nodos Left & Right**

    ---
    """)
    return


@app.cell
def _(
    And,
    Solver,
    a,
    a_,
    b,
    b_,
    dom_pc,
    lefttoerror,
    lefttoskip,
    pc,
    pc_,
    righttoerror,
    righttoskip,
    x,
    x_,
    y,
    y_,
    z,
    z_,
):
    excl = Solver()
    excl.add(dom_pc)
    excl.add(And(lefttoskip(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_),
                 lefttoerror(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_)))
    print(excl.check())   # unsat

    excr = Solver()
    excr.add(dom_pc)
    excr.add(And(righttoskip(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_),
                 righttoerror(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_)))
    print(excr.check())   # unsat
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Trans**

    ---
    """)
    return


@app.cell
def _(
    Or,
    Solver,
    a,
    a_,
    b,
    b_,
    dom_pc,
    lefttoerror,
    lefttoskip,
    n_error,
    n_init,
    n_left,
    n_right,
    n_skip,
    n_stop,
    pc,
    pc_,
    righttoerror,
    righttoskip,
    skiptoleft,
    skiptoright,
    skiptostop,
    x,
    x_,
    y,
    y_,
    z,
    z_,
):
    status2 = (pc_, x_, y_, z_, a_, b_)
    status1 = (pc, x, y, z, a, b)

    def transcfa(status1, status2):
        return Or(skiptostop(*status1, *status2), skiptoleft(*status1, *status2), skiptoright(*status1, *status2), lefttoskip(*status1, *status2), righttoskip(*status1, *status2), lefttoerror(*status1, *status2), righttoerror(*status1, *status2))


    # base: transicao possivel entre dois estados simbolicos
    t = Solver()
    t.add(dom_pc)
    t.add(transcfa(status1, status2))
    print("base", t.check())            # sat

    # estados terminais, ou seja, sem sucessor
    for namet, node in [("stop", n_stop), ("error", n_error)]:
        t.push()
        t.add(pc == node)
        print(namet, t.check())          # esperado: unsat
        t.pop()

    # cada nodo nao terminal tem sucessor
    for namet, node in [("skip", n_skip), ("left", n_left), ("right", n_right)]:
        t.push()
        t.add(pc == node)
        print(namet, t.check())          # sat
        t.pop()

    # pc_ só pode ser um nodo alcancavel por transicao (nunca init)
    t.push()
    t.add(pc_ == n_init)
    print("pc_ == init", t.check())     # unsat
    t.pop()

    print(t.assertions())               # só dom_pc e transcfa
    return (transcfa,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **BMC**

    ---
    """)
    return


@app.cell
def _(BitVec, BitVecs, Solver, initcfa, n, n_stop, sat, transcfa):
    STEPS = 6   # nº de estados na sequência (6 estados = 5 transições)

    # 1. Criar um estado (tuplo) por passo, com nomes distintos pelo índice
    def newstate(i):
        pc_i = BitVec(f'pc_{i}', 3)
        x_i, y_i, z_i, a_i, b_i = BitVecs(f'x_{i} y_{i} z_{i} a_{i} b_{i}', n)
        return (pc_i, x_i, y_i, z_i, a_i, b_i)

    nodes = [newstate(i) for i in range(STEPS)]

    # 2. Solver novo
    bmc = Solver()

    # 3. Primeiro estado satisfaz o estado inicial
    bmc.add(initcfa(*nodes[0]))

    # 4. Cada par consecutivo está ligado por transcfa
    for i in range(STEPS - 1):
        bmc.add(transcfa(nodes[i], nodes[i + 1]))

    # 5. Fixar os inputs no estado 0 (as variáveis do passo 0, não as globais)
    bmc.add(nodes[0][4] == 3)   # a
    bmc.add(nodes[0][5] == 2)   # b

    # 6. Pergunta: o último estado é stop com z == 6?
    last = nodes[-1]
    bmc.push()
    bmc.add(last[0] == n_stop, last[3] == 6)
    r = bmc.check()
    print(r)
    if r == sat:
        m = bmc.model()
        for i, e in enumerate(nodes):
            print(i, m.eval(e[0]), m.eval(e[1]), m.eval(e[2]), m.eval(e[3]))
    bmc.pop()

    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Predicado de Erro**

    ---
    """)
    return


app._unparsable_cell(
    r"""
    def perrcfa(pc):
    """,
    name="_"
)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **k-inducao**

    ---
    """)
    return


if __name__ == "__main__":
    app.run()
