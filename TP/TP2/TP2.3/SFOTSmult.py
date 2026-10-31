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
        ULT, ULE, UGT, UGE, UDiv, LShR, substitute
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


    return And, BitVec, BitVecs, Not, Solver, dom_pc, mo, n_skip, n_stop, pc


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Variáveis Globais**

    ---
    """)
    return


@app.cell
def _(BitVec, BitVecs):
    #n-bits
    n = 8

    #declaração de x,y,z
    x, y, z = BitVecs('x y z', n)

    a, b = BitVecs('a b', n)
    a_, b_ = BitVecs('a_ b_', n)
    x_, y_, z_ = BitVecs('x_ y_ z_', n)
    pc_ = BitVec('pc_', 3)

    return a, a_, b, b_, pc_, x, x_, y, y_, z, z_


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Estado Inicial**

    ---
    """)
    return


@app.cell
def _(And, Not, Solver, a, b, dom_pc, n_skip, pc, x, y, z):
    def initcfa(pc, x, y, z, a, b):
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




    return


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

    print(stss.assertions()) # só dom_pc e initcf

    
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Skip -> Left**

    ---
    """)
    return


app._unparsable_cell(
    r"""
    def skiptoleft():
    
    """,
    name="_"
)


if __name__ == "__main__":
    app.run()
