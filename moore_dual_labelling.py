import finitefield as ff
import copy
import sympy

class Point:
    # first coordinate (fc) of point is element of field F_q and second coordinate is element of Z_3. By default the
    # infinity point is created
    def __init__(self, fc=None, sc=None):
        self.fc = fc
        self.sc = sc

    def __eq__(self, other):
        if other.fc == self.fc and other.sc == self.fc:
            return True
        else:
            return False

    def add_forbidden(self, n):
        """Adds to the current point element n of the forbidden subgroup N = {0} \times \mathbb{F}_q"""
        other = copy.deepcopy(self)
        # if the current point is the infinity point
        if other.fc is None:
            return other
        else:
            other.sc = (other.sc + n) % 3
        return other

    def add_coset_rep(self, h):
        """Adds to the current point element h of the standard system of representatives H = F_q \times {0}
        of the nontrivial cosets of N in F_q \times Z_3"""
        other = copy.deepcopy(self)
        # if the current point is the infinity point
        if other.fc is None:
            return other
        else:
            other.fc = other.fc + h
        return other


class Block:
    def __init__(self, point1: Point, point2: Point, point3: Point, point4: Point):
        self.point1 = point1
        self.point2 = point2
        self.point3 = point3
        self.point4 = point4

    def __contains__(self, point):
        if self.point1 == point or self.point2 == point or self.point3 == point or self.point4 == point:
            return True
        else:
            return False

    def __eq__(self, other):
        if self.__contains__(other.point1) and self.__contains__(other.point2) and self.__contains__(other.point3) and self.__contains__(other.point4):
            return True
        else:
            return False

    def add_forbidden(self, n):
        other = copy.deepcopy(self)
        other.point1.add_forbidden(n)
        other.point2.add_forbidden(n)
        other.point3.add_forbidden(n)
        other.point4.add_forbidden(n)
        return other

    def add_coset_rep(self, h):
        other = copy.deepcopy(self)
        other.point1.add_coset_rep(h)
        other.point2.add_coset_rep(h)
        other.point3.add_coset_rep(h)
        other.point4.add_coset_rep(h)
        return other

def get_least_primitive_root(p):
    a = 2
    s = p - 1
    UF = list(set(sympy.ntheory.factorint(s)))

    while True:
        broken = False
        for i in range(len(UF)):
            if (pow(a, s//UF[i], p) == 1):
                broken = True
                break

        if broken is False:
            return a

        a += 1

def get_primitive_root(F_q, p, n):
    coefficients = [0 for _ in range(n)]
    q = p**n
    generated_elements = [0 for _ in range(q-1)]
    for _ in range(q - 1):
        # increment coefficients
        for idx in range(n-1, -1, -1):
            if coefficients[idx] < p - 1:
                coefficients[idx] += 1
                for j in range(idx + 1, n):
                    coefficients[j] = 0
                break

        x = F_q(coefficients)
        seen_elements = [0 for _ in range(q - 1)]
        broken = False
        for i in range(q-1):
            y = x**i
            y_coefficients = y.poly.coefficients
            position = 0
            for idx in range(len(y_coefficients)):
                position += int(y_coefficients[idx])*(p**idx)

            if seen_elements[position - 1] == 1:
                broken = True
                break
            else:
                seen_elements[position - 1] = 1

        if broken is False:
            return x


def get_optimal_dual_labelling(p, n):

    # begin by generating the Moore difference family from F_{p^n}
    q = p**n
    F_q = ff.FiniteField(p, n)
    t = (p**n - 1)//4
    # get primitive element x
    if n == 1:
        x = F_q(get_least_primitive_root(p))
    else:
        x = get_primitive_root(F_q, p, n)
    df_blocks = [[] for _ in range(t)]
    for i in range(t):
        df_blocks[i] = Block(Point(x**i, 0), Point(-x**i, 0), Point(x**(i + t), 1), Point(-x**(i+t), 1))

    infty_block = Block(Point(0, 0), Point(0, 1), Point(0, 2), Point())

    # cell of block labelling rk contains a block, and the index of that cell is the label assigned to the block
    # of that cell.
    rk = [[] for _ in range((3*t + 1)*(4*t + 1))]

    # implements Theorem 2.1
    if t % 2 == 0:
        for i in range(len(df_blocks)//2):
            for j in range(3):
                rk[3*i + j] = df_blocks[i].add_forbidden(j)
                rk[3*len(df_blocks) - 3*i - j] = df_blocks[len(df_blocks) - i].add_forbidden(j)

        rk[3*len(df_blocks)//2] = infty_block

        # ensure that rk is development-consistent with respect to H = F_q \times {0}
        for i in range(3*len(df_blocks) + 1):
            for j in range(q - 1):
                rk[i + j*(3*len(df_blocks) + 1)] = rk[i].add_coset_rep(x**j)

    # implements Lemma 4.8
    else:
        # get special secant
        prime_subfield_prim_root = get_least_primitive_root(p)
        s = (p - 1)//4
        for i in range(s):
            if {pow(prime_subfield_prim_root, i, p), pow(prime_subfield_prim_root, i + s, p)} <= set([x for x in range(1, p) if x <= (p-1)//4 or x >= (3*p + 1)//4]):
                secant_special_fc = [pow(prime_subfield_prim_root, i, p), -pow(prime_subfield_prim_root, i, p) % p,
                                     pow(prime_subfield_prim_root, i + s, p), -pow(prime_subfield_prim_root, i + s, p) % p]
                break

        # now determine whether the special secant is (0,1)- or (1,0)-special

        # next, we need an arbitrary polynomial-based indexing in x of F_q
        buckets = [[0 for _ in range(p)] for _ in range(p**(n - 1))]
        bucket_counts = [0 for _ in range(p**(n-1))]

        # begin by placing 0 in F_q in the first bucket
        buckets[0][bucket_counts[0]] = 0*x
        bucket_counts[0] += 1

        for i in range(q - 1):
            y = x**i
            y_coefficients = y.poly.coefficients
            bucket_num = 0
            for j in range(1, len(y_coefficients)):
                bucket_num += int(y_coefficients[j])*(p**(j-1))
            buckets[bucket_num][bucket_counts[bucket_num]] = y
            bucket_counts[bucket_num] += 1

        # now refine the polynomial-based indexing
        buckets_refined = [[0 for _ in range(p)] for _ in range(p**(n - 1))]
        for i in range(p**(n-1)):
            if (i % 2) == 0:
                for j in range(p):
                    for field_ele in buckets[i]:
                        if field_ele.poly.coefficients == []:
                            pass
                        elif int(field_ele.poly.coefficients[0]) == j:
                            buckets_refined[i][j] = field_ele
                            break
            else:
                for j in range(p):
                    for field_ele in buckets[i]:
                        if int(field_ele.poly.coefficients[0]) == p - 1 - j:
                            buckets_refined[i][j] = field_ele
                            break
        del buckets

        # Now it's time to construct the block labelling rk. We do it in the following order (see the 10 conditions
        # C1 - C10 in the proof of Lemma 4.8): C3 -> C4 -> C5 -> C6 -> C2 -> C7 -> C8 -> C9 -> C10
        if n == 1:
            secant_special = Block(Point(F_q(secant_special_fc[0]), 0), Point(F_q(secant_special_fc[1]), 0), Point(F_q(secant_special_fc[2]), 1), Point(F_q(secant_special_fc[3]), 1))
        else:
            secant_special = Block(Point(F_q([secant_special_fc[0]] + [0 for _ in range(n-1)]), 0), Point(F_q([secant_special_fc[1]] + [0 for _ in range(n-1)]), 0), Point(F_q([secant_special_fc[2]] + [0 for _ in range(n-1)]), 0), Point(F_q([secant_special_fc[3]] + [0 for _ in range(n-1)]), 0))

        unused_base_blocks_idxs = [_ for _ in range(len(df_blocks))]

        # find the special secant in the Moore difference family and mark it as used
        for idx, block in enumerate(df_blocks):
            if secant_special.__eq__(block):
                unused_base_blocks_idxs.pop(unused_base_blocks_idxs.index(idx))
                break

        # C3
        block_current = df_blocks[unused_base_blocks_idxs.pop()]
        rk[0] = block_current
        rk[1] = block_current.add_forbidden(2)
        rk[2] = block_current.add_forbidden(1)

        # C4
        block_current = df_blocks[unused_base_blocks_idxs.pop()]
        rk[3*t - 2] = block_current.add_forbidden(2)
        rk[3*t - 1] = block_current.add_forbidden(1)
        rk[3*t] = block_current

        # C5
        for j in range(1, (t-3)//2 + 1):
            block_current_1 = df_blocks[unused_base_blocks_idxs.pop()]
            block_current_2 = df_blocks[unused_base_blocks_idxs.pop()]
            for k in range(3):
                rk[3*j + k] = block_current_1.add_forbidden(k)
                rk[3*t - 3*j - k] = block_current_2.addforbidden(k)

        # C6
        if is_0_1_special:
            rk[(3 * t - 3) // 2] = secant_special.add_forbidden(1)
            rk[(3 * t + 3) // 2] = secant_special.add_forbidden(2)
        else:
            rk[(3 * t - 3) // 2] = secant_special.add_forbidden(2)
            rk[(3 * t + 3) // 2] = secant_special.add_forbidden(1)

        # C2
        for i in [_ for _ in range(3*t + 1) if _ <= (3*t-3)//2 or _ >= (3*t + 3)//2]:
            for j in range(p**(n-1)):
                for k in range(p):
                    rk[i + j*(3*t + 1)] = rk[i].add_coset_rep(buckets_refined[j][k])









