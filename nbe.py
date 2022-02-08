def interp(expr):
    if isinstance(expr, tuple):
        return interp(expr[0])[1](interp(expr[1]))
    elif expr == "S":
        return ("S",
            lambda a: (("S", a[0]),
                lambda b: (("S", a[0], b[0]),
                    lambda c: (a[1](c)) [1] (b[1](c)))))
    elif expr == "K":
        return ("K", lambda a: (("K", a[0]), lambda _: a))
    else:
        raise ValueError("Invalid expression:", expr)

test = ((("S", "K"), "K"), "K")
if __name__=="__main__":
    print(interp(test)[0])
