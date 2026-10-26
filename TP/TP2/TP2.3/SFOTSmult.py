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


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    #TP1.1

    ##Grupo 19
    João Pontes, A111657

    João Paulo, A110393

    Objetivo:
        1. Construir um SFOTS, usando BitVec’s de tamanho n , que descreva o comportamento de um dado CFA (Control Flow Automaton);
        2. Usando k-indução verificar nesse SFOTS se a propriedade (x*y + z = a*b) é um invariante do seu comportamento.
        3. Usando k-indução no SFOTS acima e adicionando ao estado inicial  a condição (a < 2^{n/2}) ∧ (b < 2^{n/2}), verificar a segurança do programa;
        4. Codificar a propriedade de animação que exprime que o programa termina quaisquer que sejam os valores iniciais de a e b e prove que ela se verifica no SFOTS.

    ---
    """)
    return


@app.cell
def _():
    import marimo as mo
    from z3 import(
        BitVec, BitVecs, BitVecVal, Const, EnumSort, Solver,
        And, Or, Not, If, simplify, sat, unsat,
        ULT, ULE, UGT, UGE, UDiv, LShR, substitute
    )


    _init = BitVecVal(1,3)
    _skip = BitVecVal(2,3)
    _left = BitVecVal(3,3)
    _right = BitVecVal(4,3)
    _stop = BitVecVal(5,3)
    _error = BitVecVal(6,3)

    pc = BitVec('pc', 3)

    dom_pc = And(ULE(1,pc), UGE(6,pc))

    for k in range(8):
        print(k, simplify(substitute(dom_pc, (pc, BitVecVal(k, 3)))))

    s = Solver()
    s.add(dom_pc)
    s.add(pc == 7)
    print(s.check())

    return (mo,)


if __name__ == "__main__":
    app.run()
