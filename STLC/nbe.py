fresh = 0

def reflect(prog):
    return lambda: (lambda: prog, lambda x: reflect(("app", reflect(prog), x)))

def interpret(prog, env):
    global fresh
    if isinstance(prog, str):
        return env[prog]
    elif prog[0] == "lam":
        fresh += 1
        name = "x" + str(fresh)
        body = lambda x : interpret(prog[2], {**env, prog[1]: x})
        return lambda: (lambda: ("lam", name, body(reflect(name))), body)
    elif prog[0] == "app":
        return lambda: interpret(prog[1], env)()[1](interpret(prog[2], env))()

def reify(sem):
    sem = sem()
    if isinstance(sem[0], str):
        return sem[0]
    body = sem[0]()
    if body[0] == "lam":
        return ("lam", body[1], reify(body[2]))
    elif body[0] == "app":
        return ("app", reify(body[1]), reify(body[2]))

def evaluate(prog):
    return reify(interpret(prog, {}))

I = ("lam", "x", "x")
K = ("lam", "x", ("lam", "y", "x"))
TT = K
S = ("lam", "x", ("lam", "y", ("lam", "z", ("app", ("app", "x", "z"), ("app", "y", "z")))))
SKK = ("app", ("app", S, K), K)
omega = ("lam", "x", ("app", "x", "x"))
Y = ("lam", "f",
    ("app",
        ("lam", "x", ("app", "f", ("app", "x", "x"))),
        ("lam", "x", ("app", "f", ("app", "x", "x")))))
Zero = ("lam", "x", ("lam", "y", "y"))
FF = Zero
Succ = ("lam", "n",
    ("lam", "f",
        ("lam", "x",
            ("app", "f",
                ("app", ("app", "n", "f"), "x")))))
def getNumber(n):
    if n == 0: return Zero
    else: return ("app", Succ, getNumber(n-1))
def toNumber(prog):
    number = -2
    while isinstance(prog, tuple):
        number += 1
        prog = prog[2]
    return number
Add = ("lam", "m", ("lam", "n",
    ("lam", "f", ("lam", "x",
        ("app", ("app", "m", "f"), ("app", ("app", "n", "f"), "x"))))))
Mult = ("lam", "m", ("lam", "n",
    ("lam", "f",
        ("app", "m", ("app", "n", "f")))))
Exp = ("lam", "m", ("lam", "n", ("app", "n", "m")))
IsZero = ("lam", "n", ("app", ("app", "n", ("app", K, FF)), TT))
Pred = ("lam", "n", ("lam", "f", ("lam", "x",
    ("app", ("app", ("app", "n",
        ("lam", "g", ("lam", "h", ("app", "h", ("app", "g", "f"))))),
        ("lam", "u", "x")),
        ("lam", "u", "u")))))
Fact = ("app", Y, ("lam", "f",
    ("lam", "n",
        ("app", ("app", ("app", IsZero, "n"),
            getNumber(1)),
            ("app", ("app", Mult, "n"), ("app", "f", ("app", Pred, "n")))))))

if __name__ == "__main__":
    print(toNumber(evaluate(
        ("app", Fact, getNumber(5))
    )))
