"""Independent finite check for the v2.6.1 editorial correction.

No dependencies. Not a Lean proof; this script checks two explicit finite models.
"""
from itertools import product


def local(left, center, right):
    return (110 >> (4 * left + 2 * center + right)) & 1


def ring(state):
    return tuple(local(state[i-1], state[i], state[(i+1) % len(state)])
                 for i in range(len(state)))


def clamped(state):
    cells = (1,) + state + (0,)
    return tuple(local(*cells[i:i+3]) for i in range(4))


def word(state):
    return ''.join(map(str, state))


def bits(s):
    return tuple(map(int, s))


def canonical_cycle(cycle):
    return min(cycle[i:] + cycle[:i] for i in range(len(cycle)))


def main():
    initial = state = bits('00010011011111')
    ports, boundary = [], []
    for _ in range(7):
        ports.append(word(state[3:7]))
        boundary.append(f'{state[2]}{state[7]}')
        state = ring(state)
    assert state == initial
    assert boundary == ['01', '11', '10', '00', '01', '01', '11']
    assert ports == ['1001', '1011', '1110', '0010', '0110', '1111', '1000']
    assert len(set(ports)) == 7
    assert word(clamped(bits('1011'))) == '1111' != ports[2]
    assert word(clamped(bits('0111'))) == '1101'
    assert clamped(clamped(bits('0111'))) == bits('0111')
    assert local(0, 0, 0) != local(0, 0, 1)
    cycles = set()
    for state in product(range(2), repeat=4):
        trajectory = []
        while state not in trajectory:
            trajectory.append(state)
            state = clamped(state)
        cycles.add(canonical_cycle(tuple(map(word, trajectory[trajectory.index(state):]))))
    assert cycles == {('0000',), ('1000',), ('0100', '1100'),
                      ('0111', '1101'), ('0010', '0110', '1110')}
    print('Free orbit:', ' -> '.join(ports + [ports[0]]))
    print('Boundaries:', ' '.join(boundary))
    print('Clamped cycles:', sorted(cycles))
    print('PASS: free/clamped mismatch and two-step clamped return')


if __name__ == '__main__':
    main()
