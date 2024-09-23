using Random
using Test

# make BigFloat big enough to hold floatmax() as an integer
setprecision(1024)

function test_example(
    ::Type{T},
    A::BigInt,
    S::BigInt,
    B::BigInt,
    D::BigInt,
    x::T,
) where {T<:AbstractFloat}
    @show (A, S, B, D, x)
    (a, s, b) = map(T, (A/D + x, S/D, B/D + x))
    r = lift_range(a, s, b)
    R = A:S:B
    l = length(R)
    @test max(-1, r.n) == l-1
    @test first(r) == a
    @test step(r) == s
    @test last(r) == b
    @test r[1] == a
    l ≤ typemax(Int) || return
    @test length(r) == l
    @test r[l] == b
    i = searchsortedfirst(R, 0)
    for j = i-10:i+10
        1 ≤ j ≤ l || continue
        # comparison is exact at zero
        @test r[j] - T(R[j]/D) ≈ x
    end
end

macro test_example(ex)
    ex isa Expr && ex.head == :tuple && length(ex.args) == 5 ||
        error("invalid @test_example call: $ex")
    map!(ex.args, ex.args) do arg
        arg isa AbstractString ? :(BigFloat($arg)) : esc(arg)
    end
    quote
        t = $ex
        test_example(
            Float64,
            BigInt(t[1]),
            BigInt(t[2]),
            BigInt(t[3]),
            BigInt(t[4]),
            Float64(t[5]),
        )
    end
end

Random.seed!(0)
rands = randn(10)
shifts = [0; π; ℯ; rands]

for x in shifts, a in [3, 1, -1, -3]
    @test_example a, 2, 19, 10, x
end

# TODO (broken, ratio consistency):
# for a = -10:10, s = 1:10, n = 0:10, d = 1:19, x in shifts
#     @test_example a, s, a+n, d, x
# end

function base_examples(d, x)
    @test_example  -1,  1,  0, d, x
    @test_example  -2,  1,  0, d, x
    @test_example  -3,  1,  0, d, x
    @test_example -19,  1,  0, d, x
    @test_example   0,  1,  1, d, x
    @test_example   0,  1,  2, d, x
    @test_example   0,  1,  3, d, x
    @test_example   0,  1, 19, d, x
    @test_example   1,  1,  3, d, x
    @test_example   0,  1,  3, d, x
    @test_example   3, -1, -1, d, x
    @test_example   1, -1, -3, d, x
    @test_example   0,  1, 10, d, x
    @test_example   0,  7, 21, d, x
    @test_example   0, 11, 33, d, x
    @test_example   1, 11, 34, d, x
    @test_example   0, 13, 39, d, x
    @test_example   1, 13, 40, d, x
    @test_example  11, 11, 33, d, x
    @test_example   3,  1, 11, d, x
    @test_example   0,  1,  5, d, x
end

for d = 1:1000
    base_examples(d, 0)
end

for d = 1:100, x = shifts
    base_examples(d, x)
end

@test_example 0, 15, 42000, 100, 0
@test_example 49, 1, 1323, 49, 0

@test_example  "-3e50", "1e50", "4e50", 1, 0
@test_example  "-3e50", "1e50", "4e50", "1e25", 0
@test_example  "-3e50", "1e50", "4e50", "1e50", 0
@test_example  "-3e50", "1e50", "4e50", "1e60", 0

@test_example  "-1e20", "3", "2e20", 1, 0
@test_example  "-1e20", "3", "2e20", "1e10", 0
@test_example  "-1e20", "3", "2e20", "1e20", 0
@test_example  "-1e20", "3", "2e20", "1e30", 0

@test_example "-1e18", "3", "2e19", 1, 0
@test_example "-1e18", "3", "2e19", 10, 0
@test_example "-1e18", "3", "2e19", "1e9", 0
@test_example "-1e18", "3", "2e19", "1e17", 0
@test_example "-1e18", "3", "2e19", "1e18", 0
@test_example "-1e18", "3", "2e19", "1e19", 0
@test_example "-1e18", "3", "2e19", "1e20", 0

@test_example "-1e15", "9", "8e16", 1, 0
@test_example "-1e15", "9", "8e16", 10, 0
@test_example "-1e15", "9", "8e16", "1e5", 0
@test_example "-1e15", "9", "8e16", "1e10", 0
@test_example "-1e15", "9", "8e16", "1e14", 0
@test_example "-1e15", "9", "8e16", "1e15", 0
@test_example "-1e15", "9", "8e16", "1e16", 0
@test_example "-1e15", "9", "8e16", "1e17", 0

# subnormal ranges
@test_example -10, 5, 15, "1e324", 0
@test_example   0, 5, 15, "1e324", 0
@test_example -15, 5,  0, "1e324", 0

# TODO (broken, subnormal):
# @test_example 3, 2, 19, "1e310", 0.0

# TODO (broken, near infinity):
# lift_range(-floatmax(T), floatmax(T)/10, floatmax(T))
