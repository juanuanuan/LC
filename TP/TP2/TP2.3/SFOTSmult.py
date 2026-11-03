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
    **Nodos e domínio do `pc`**

    ---

    O identificador do nodo é um `BitVec` de 3 bits, com uma constante por nodo do CFA:
    `init=1`, `skip=2`, `left=3`, `right=4`, `stop=5`, `error=6`.
    Os nomes só existem no código Python (prefixo `n_`); para o Z3 são apenas números.

    Com 3 bits há 8 valores e só 6 são nodos válidos. O predicado `dom_pc` restringe o `pc` a $1 \le pc \le 6$,
    com comparações **sem sinal** (`ULE`/`UGE`). O teste com `substitute` + `simplify` confirma que é `True` só para 1 a 6.
    Mais à frente o `dom` é imposto a todos os estados do passo indutivo, para o solver não escolher `pc = 0` ou `7`.
    """)
    return


@app.cell
def _():
    #init dos nodos do CFA
    import marimo as mo
    from z3 import(
        BitVec, BitVecs, BitVecVal, Const, EnumSort, Solver,
        And, Or, Not, If, simplify, sat, unsat,
        ULT, ULE, UGT, UGE, UDiv, LShR, substitute, ZeroExt, Extract, Implies
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
        Implies,
        Not,
        Or,
        Solver,
        UDiv,
        UGE,
        ULE,
        ULT,
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
    **Variáveis Globais**

    O estado do SFOTS é o tuplo $(pc, x, y, z, a, b)$, por esta ordem em todas as funções.
    `x, y, z, a, b` têm $n$ bits (aqui $n=8$, definido num só sítio) e `pc` tem 3.
    `a` e `b` fazem parte do estado porque o invariante $x*y+z=a*b$ os usa; nunca mudam (frame condition).
    As variáveis com sufixo `_` (`x_`, `pc_`, ...) representam o **estado seguinte**, necessário para escrever a relação de transição.

    **Overflow check**

    Em Z3 as operações sobre `BitVec` são módulo $2^n$ e nunca assinalam erro, ao contrário de uma ALU.
    O overflow tem de ser detetado à mão: `ovfl_add(u, v)` faz a soma em $n+1$ bits (`ZeroExt(1, ...)`)
    e verifica o bit extra (o "vai um"). Se for 1, o resultado verdadeiro não cabe em $n$ bits.
    Usa-se `ovfl_add(x, x)` para $x \ll 1$ (ramo `left`) e `ovfl_add(z, x)` para $z + x$ (ramo `right`).
    A função usa `u.size()`, por isso não depende da global `n`

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

    `initcfa` impõe $pc = skip \land x = a \land y = b \land z = 0$.

    **Decisão de modelação:** o estado inicial do SFOTS é o estado do CFA *depois* de executar a ação do nodo `init`.
    Esse nodo não tem antecedentes nem guarda e é determinístico, por isso a sua atribuição $x,y,z \leftarrow a,b,0$
    pode ser absorvida no predicado inicial sem alterar os comportamentos. Consequências: o nodo `init` não aparece na
    relação de transição, e o invariante $x*y+z=a*b$ vale desde o primeiro estado.

    **Validação:** com `dom_pc` + `initcfa` o solver dá `sat`. Cada negação (`pc`, `x`, `y`, `z`), testada isoladamente
    com `push()`/`pop()`, dá `unsat`, o que prova que a função impõe cada uma das quatro condições.

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

    Guarda: $pc = skip \land y = 0$. Estado seguinte: $pc' = stop$.
    A seta do diagrama só tem uma **condição** ($y=0$), não uma atribuição, por isso nenhuma variável muda:
    $x'=x,\ y'=y,\ z'=z$, e $a'=a,\ b'=b$ (frame condition, comum a todos os ramos).

    Validação: base `sat`; negar `pc_`, qualquer variável de dados ou a guarda $y=0$ dá `unsat`.

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

    Guarda: $pc = skip \land y \neq 0 \land even(y)$. Estado seguinte: $pc' = left$.
    A paridade testa-se pelo bit menos significativo: $y$ é par sse $(y \,\&\, 1) = 0$.

    No diagrama, a atribuição $x,y,z \leftarrow 2x, y/2, z$ está **dentro do nodo `left`**, não na seta.
    Modelámos isso fazendo a ação na saída de `left` (ramo `left → skip`); por isso aqui os dados não mudam.
    A condição $y \neq 0$ é necessária porque $0$ também é par, e sem ela `skip` deixava de ser determinístico
    (`skip→stop` e `skip→left` aplicavam-se em simultâneo).

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

    Guarda: $pc = skip \land y \neq 0 \land odd(y)$, com $odd(y)$ dado por $(y \,\&\, 1) \neq 0$.
    Estado seguinte: $pc' = right$, com os dados inalterados (a ação é aplicada em `right → skip`).

    As guardas dos três ramos de `skip` ($y=0$; $y\neq0$ par; $y\neq0$ ímpar) são mutuamente exclusivas e cobrem
    todos os casos, logo `skip` é determinístico. Nota: $y \neq 0$ é redundante com "ímpar", mas espelha o diagrama.
    Por essa razão o teste "negar $y\neq0$" é fraco (já dava `unsat` pela paridade).

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

    Guarda: $pc = left \land \neg overflow(x \ll 1)$, ou seja `Not(ovfl_add(x, x))`.
    Ação: $x' = 2x,\ y' = y/2,\ z'=z$.

    A divisão é **sem sinal** (`UDiv`), porque os dados são inteiros sem sinal; `/` em `BitVec` é com sinal.
    Sem a guarda de overflow, o módulo $2^n$ deixava este ramo aplicar-se mesmo quando $2x$ não cabe em $n$ bits,
    e o estado de erro nunca seria atingido (a alínea 3 passaria por vacuidade).

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
        ("ovfl", (ovfl_add(x,x))), # Not(Not(ovfl_add(x,x)))
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

    Guarda: $pc = right \land \neg overflow(z + x)$.
    Ação: $x'=x,\ y'=y-1,\ z'=z+x$.

    O overflow a controlar é o da soma $z+x$; $y-1$ não precisa de guarda, porque em `right` o $y$ é ímpar (logo $\ge 1$)
    e a subtração não dá a volta. Esse facto só é garantido nos estados **alcançáveis**; num estado arbitrário
    $y=0$ daria $255$. É por isso que a prova da alínea 4 precisa de um invariante auxiliar ($y \neq 0$ em `left`/`right`).

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

    Guarda: $pc = left \land overflow(x \ll 1)$. Estado seguinte: $pc' = error$.
    É o complemento exato de `left → skip`: o overflow tem **precedência** sobre o ramo normal, como pede o enunciado.
    Os dados mantêm-se (a ação não chegou a completar-se). `error` não tem ramos de saída: é um estado terminal.

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

    Guarda: $pc = right \land overflow(z + x)$. Estado seguinte: $pc' = error$, com os dados inalterados.
    Complemento de `right → skip`, e tal como `error` em `left`, é terminal.

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

    Em `left` e em `right` há dois ramos possíveis (normal e erro). Para o autómato ser determinístico nesses nodos,
    os dois ramos não podem aplicar-se ao mesmo tempo. O teste adiciona `And(lefttoskip, lefttoerror)` (e o análogo para `right`)
    e espera `unsat`: as guardas $\neg overflow$ e $overflow$ são contraditórias, logo nunca coexistem.

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
    **Relação de transição**

    `transcfa(s, s')` é a disjunção dos **sete** ramos: `skip→stop`, `skip→left`, `skip→right`, `left→skip`,
    `right→skip`, `left→error`, `right→error`. Cada ramo é um `And` com guarda, atualização do `pc`, dos dados e frame condition.
    O ramo `init` não existe (ver estado inicial). Cada estado é um tuplo e as funções dos ramos recebem argumentos soltos,
    por isso desempacota-se com `*`.

    **Validações:**
    - existe transição entre dois estados simbólicos (`sat`);
    - `stop` e `error` não têm sucessor (`unsat`): são terminais;
    - `skip`, `left` e `right` têm sucessor (`sat`);
    - nenhum ramo leva a `init` (`unsat`).

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
        print(namet, t.check())          # unsat
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
    **Predicado de Erro**

    `perrcfa` diz que o estado é de erro: $pc = error$. É uma propriedade de **um** estado.
    Não entra na `transcfa` (os ramos de overflow já levam $pc'=error$); serve para formular a segurança
    (`Not(perrcfa)` em todos os estados) e para perguntar ao BMC se o erro é alcançável.

    ---
    """)
    return


@app.cell
def _(Not, Solver, a, b, dom_pc, n_error, pc, x, y, z):
    def perrcfa(pc, x, y, z, a, b):
        return pc == n_error #se o estado é erro


    errs = Solver()
    errs.add(dom_pc)
    errs.add(perrcfa(pc, x, y, z, a, b))
    print(errs.check()) # sat neste caso

    for name8, neg8 in [
        ("pc",  Not(pc == n_error))   
    ]:
        errs.push()
        errs.add(neg8)
        print(name8, errs.check()) # unsat em todos os restantes
        errs.pop()

    print(errs.assertions()) 

    #print(type(n_error), n_error)
    return (perrcfa,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Model Check**

    Com $n=8$, $a=b=5$ e `STEPS = 10` verifica-se:
    1. existe execução que termina em `stop` com $z=25=5\cdot5$ (`sat`): o modelo implementa a multiplicação,
       seguindo o caminho `skip → right → skip → left → skip → left → skip → right → skip → stop`;
    2. o erro não é alcançável (`unsat`): o maior valor que aparece é 25, longe de $2^8-1$.

    **Limitação:** o MC só diz o que acontece até à profundidade testada. Para não passar por vacuidade, o erro foi confirmado
    com $n=4$, $a=b=5$ e 7 estados (`sat`: $2\cdot 10 > 15$). A prova para qualquer profundidade é a k-indução.

    ---
    """)
    return


@app.cell
def _(BitVec, BitVecs, Or, Solver, initcfa, n, n_stop, perrcfa, sat, transcfa):
    STEPS = 10   # num de estados na sequência (10 estados)

    # indexação das variáveis por estado/nodo
    def newstate(i, tag = ''):
        pc_i = BitVec(f'pc_{i}', 3)
        x_i, y_i, z_i, a_i, b_i = BitVecs(f'x_{i} y_{i} z_{i} a_{i} b_{i}', n)
        return (pc_i, x_i, y_i, z_i, a_i, b_i)

    nodes = [newstate(i, 'bmc') for i in range(STEPS)]

    # bmc solver
    bmc = Solver()

    # estado init
    bmc.add(initcfa(*nodes[0]))

    # cada par consecutivo está ligado por transcfa
    for i in range(STEPS - 1):
        bmc.add(transcfa(nodes[i], nodes[i + 1]))

    # fixação de input
    bmc.add(nodes[0][4] == 5)   # a
    bmc.add(nodes[0][5] == 5)   # b

    last = nodes[-1]
    bmc.push()
    bmc.add(last[0] == n_stop, last[3] == 25) # valor de z no stop
    r = bmc.check()
    print(r)
    if r == sat:
        m = bmc.model()
        for i, e in enumerate(nodes):
            print(i, m.eval(e[0]), m.eval(e[1]), m.eval(e[2]), m.eval(e[3]))
    bmc.pop()

    bmc.push()
    bmc.add(Or([perrcfa(pc, x, y, z, a, b) for pc, x, y, z, a, b in nodes]))
    r = bmc.check()
    print(r)
    if r == sat:
        m = bmc.model()
        for i, e in enumerate(nodes):
            print(i, m.eval(e[0]), m.eval(e[1]), m.eval(e[2]), m.eval(e[3]))
    bmc.pop()
    return (newstate,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **k-indução**

    Sejam $I$ o estado inicial, $T$ a transição e $P$ a propriedade. `kind(k, prop)` faz duas verificações:

    - **Caso base:** não existe sequência $s_0\ldots s_{k-1}$ com $I(s_0)$ e $T(s_i,s_{i+1})$ em que algum $P(s_i)$ falhe (`unsat`).
    - **Passo indutivo:** não existe sequência de $k+1$ estados **arbitrários** (sem $I$, mas com `dom_pc`) ligados por $T$,
      com $P$ nos primeiros $k$ e $\neg P$ no último (`unsat`).

    Base `unsat` + passo `unsat` ⇒ $P$ vale em todos os estados alcançáveis. Se o passo der `sat` mas a base `unsat`, é inconclusivo:
    o contra-exemplo pode partir de um estado inalcançável.

    **Resultados** (todos com base `unsat`; o passo dá `sat` em $k=1$ e `unsat` para $k\ge 2$, exceto o último):

    | Propriedade | Passo $k=1$ | Passo $k\ge2$ |
    |---|---|---|
    | $x*y+z=a*b$ (alínea 2) | `sat` | `unsat` |
    | mesma igualdade em $2n$ bits (`stronginvariant`) | `sat` | `unsat` |
    | erro nunca acessível (alínea 3) | `sat` | `unsat` |
    | $y\neq0$ em `left`/`right` | `unsat` | `unsat` |

    **Porque falha $k=1$:** os contra-exemplos são estados inalcançáveis. No invariante da alínea 2, `left` com $y$ ímpar:
    $y/2$ perde o resto e $2x\cdot(y/2)=x(y-1)\ne xy$. Nas outras, `right` com $y=0$. Com $k=2$ o estado anterior é forçado
    a ser `skip` com a guarda certa e esses estados desaparecem. Logo, o invariante é **2-indutivo**.

    **Alínea 3 e invariante auxiliar:** a igualdade módulo $2^n$ não chega, porque o solver encontra estados com $a=b=0$ e
    $x*y+z\equiv0 \pmod{2^n}$ mas $x$ enorme (overflow possível). A versão em $2n$ bits (`stronginvariant`) vale em inteiros;
    com $a,b<2^{n/2}$ tem-se $a*b<2^n$, logo $2x\le a*b$ em `left` e $z+x\le a*b$ em `right`, e o overflow não ocorre.
    O auxiliar foi provado à parte antes de ser usado como hipótese (`hyp`).

    **Nota:** as restrições $a,b<2^{n/2}$ estão impostas em todos os casos, também na alínea 2, onde o enunciado não as exige.

    ---
    """)
    return


@app.cell
def _(
    And,
    Implies,
    Not,
    Or,
    Solver,
    UGE,
    ULE,
    ULT,
    ZeroExt,
    initcfa,
    n,
    n_left,
    n_right,
    newstate,
    perrcfa,
    sat,
    transcfa,
):
    def invariant(pc, x, y, z, a, b):
        return (x * y + z == a* b)

    def stronginvariant(pc, x, y, z, a, b):
        X, Y, Z = ZeroExt(n, x), ZeroExt(n, y), ZeroExt(n, z)
        A, B = ZeroExt(n, a), ZeroExt(n, b)
        return X * Y + Z == A * B

    def dom(ppc):
        return And(ULE(1,ppc), UGE(6,ppc))

    def kind(k, prop, hyp=None, tag='', restrict=True):
        # prop(*estado) -> proposição a ser validada; hyp(*estado) -> hipótese assumida como verdade para todo o k
        lim = 2 ** (n // 2) #restrição alínea c

        # ---------- caso base ----------
        knodes = [newstate(m, tag + 'base') for m in range(k)]
        sbase = Solver()
        sbase.add(initcfa(*knodes[0]))
        if restrict:
            sbase.add(ULT(knodes[0][4], lim), ULT(knodes[0][5], lim))
        for t in range(k - 1):
            sbase.add(transcfa(knodes[t], knodes[t + 1]))
        sbase.add(Or([Not(prop(*e)) for e in knodes]))
        rbase = sbase.check()

        # ---------- passo indutivo ----------
        kn = [newstate(u, tag + 'ind') for u in range(k + 1)]
        sind = Solver()
        for e in kn:
            sind.add(dom(e[0]))
            if restrict:
                sind.add(ULT(e[4], lim), ULT(e[5], lim))
        for j in range(k):
            sind.add(transcfa(kn[j], kn[j + 1]))
        for e in kn[:-1]:
            sind.add(prop(*e))
            if hyp is not None:
                sind.add(hyp(*e))
        sind.add(Not(prop(*kn[-1])))
        rind = sind.check()

        if rind == sat:
            m = sind.model()
            for e in kn:
                print([m.eval(c) for c in e])

        return rbase, rind

    def safe(pc, x, y, z, a, b):          # erro nunca acessível
        return Not(perrcfa(pc, x, y, z, a, b))

    def y_nonzero(pc, x, y, z, a, b):     # auxiliar da alínea 4
        return And(Implies(pc == n_left,  y != 0),
                   Implies(pc == n_right, y != 0))

    for o in range(1, 6): print('b) unrestricted', o, kind(o, invariant, restrict=False))
    for o in range(1, 6): print('strong   ', o, kind(o, stronginvariant))
    for o in range(1, 6): print('c) ', o, kind(o, safe, hyp=stronginvariant))
    for o in range(1, 6): print('y != 0   ', o, kind(o, y_nonzero))
    return (dom,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Terminação (alínea 4)**

    K-indução só prova propriedades de segurança, por isso a terminação reduz-se a um argumento com **função variante**:
    a medida é $y$, inteiro sem sinal, logo limitado inferiormente por 0.

    `variant` é uma propriedade sobre **pares** de estados ligados por `transcfa`:
    - em `skip`, $y' \le y$ (nunca aumenta);
    - ao sair de `left` ou `right` para `skip`, com $y\neq0$, tem-se $y' < y$ ($y/2<y$ e $y-1<y$).

    O solver confirma que `transcfa ∧ dom ∧ ¬variant` é `unsat`. A condição $y\neq0$ em `left`/`right` não é assumida:
    foi provada por k-indução (`y_nonzero`, 1-indutiva), porque só se entra nesses nodos vindo de `skip` com $y\neq0$
    e nenhum ramo de `skip` altera $y$. A guarda $pc'=skip$ exclui as transições de overflow, que não são voltas do ciclo.


    ---
    """)
    return


@app.cell
def _(
    And,
    Implies,
    Not,
    Or,
    Solver,
    ULE,
    ULT,
    a,
    a_,
    b,
    b_,
    dom,
    n_left,
    n_right,
    n_skip,
    pc,
    pc_,
    sat,
    transcfa,
    x,
    x_,
    y,
    y_,
    z,
    z_,
):
    def variant(pc, x, y, z, a, b, pc_, x_, y_, z_, a_, b_):
        return And(
            Implies(And(Or(pc == n_left, pc == n_right),y != 0,pc_ == n_skip),ULT(y_, y)), Implies(pc == n_skip, ULE(y_, y))    # em skip, y não aumenta
        )


    est  = (pc,  x,  y,  z,  a,  b)
    est_ = (pc_, x_, y_, z_, a_, b_)

    sv = Solver()
    sv.add(dom(pc), dom(pc_))
    sv.add(transcfa(est, est_))
    sv.add(Not(variant(*est, *est_)))
    print(sv.check())   # esperado: unsat

    if sv.check() == sat:
        print(sv.model()) 
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Conclusão:** $y$ nunca aumenta e desce estritamente em cada volta por `left` ou `right`; como não pode descer
    indefinidamente, o ciclo só roda um número finito de vezes. Com $y=0$ o único ramo de `skip` é `skip → stop`.
    Logo toda a execução chega a `stop` ou a `error`, ambos terminais, e `error` não ocorre quando $a,b<2^{n/2}$ (alínea 3).
    A vivacidade decorre da boa fundação de $y$ (argumento fora do solver), apoiada nas propriedades de segurança verificadas.

    ---
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Utilização de LLM's
        1. Esclarecimento de dúvidas
        2. Análise de código e a sua eventual correção
        3. Aconcelhamento do workflow a seguir.

    ####O modelo de AI utilizado foi o `Claude`
    ---
    """)
    return


if __name__ == "__main__":
    app.run()
