import functools

@functools.total_ordering
class NumType:
    def __init__(self, bits, signed, isfloat):
        self.bits = bits
        self.signed = signed
        self.isfloat = isfloat

        if self.isfloat:
            assert signed
            self.name = f"f{bits}"
            if bits == 32:
                self.int_min = -2**24
                self.int_max = 2**24
            else:
                assert bits == 64
                self.int_min = -2**53
                self.int_max = 2**53
        else:
            if signed:
                self.name = f"i{bits}"
                self.int_min = -2**(bits-1)
                self.int_max = 2**(bits-1) - 1
            else:
                self.name = f"u{bits}"
                self.int_min = 0
                self.int_max = 2**bits

    def is_subset_eq(self, other):
        return other.int_min <= self.int_min <= self.int_max <= other.int_max

    def __lt__(self, other):
        return (self.isfloat, self.bits, self.signed) < (other.isfloat, other.bits, other.signed)

    def __repr__(self):
        return self.name
                

if __name__ == "__main__":
    types = [
        NumType(bits, signed, False)
        for bits in [8, 16, 32, 64, 128]
        for signed in [False, True]]
    types += [NumType(32, True, True), NumType(64, True, True)]

    def implies(a, b):
        return not a or b

    def common_type(a, b):
        return min((t for t in types
                    if (a.is_subset_eq(t) and b.is_subset_eq(t))
                    and implies(a.isfloat or b.isfloat, t.isfloat)), default=None)

    unhandled = []
    for a in types:
        for b in types:
            if a < b:
                c = common_type(a, b)
                if c is not None:
                    if implies(c.bits == 128, a.bits == 128 or b.bits == 128):
                        print(f"{a}, {b} => {c};")
                else:
                    unhandled.append((a, b))

    for a, b in unhandled:
        print("NO COMMON TYPE", a, b)

