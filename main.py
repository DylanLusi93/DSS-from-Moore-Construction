import sympy
import moore_dual_labelling as mdl
if __name__ == '__main__':
    while True:
        q = input("Enter a prime power q = p^n = 4t + 1 such that if t is odd then p >= 13: ")
        q = int(q)
        f = sympy.ntheory.factorint(q)
        p = list(f.keys())[0]
        n = f[list(f)[0]]
        if len(set(f)) > 1:
            print("Error: q is not a prime power! Try again.")
            continue
        if ((q - 1) % 4 == 0):
            t = q//4
            if t % 2 == 1 and p < 13:
                print("Error: Remember that if t is odd then p >= 13. Try again.")
                continue
        else:
            print("Error: q is not 1 mod 4! Try again.")
            continue

        mdl.get_optimal_dual_labelling(p, n)
        break
