using Random
using Test

Random.seed!(0)
rands = randn(10)
shifts = [0; π; ℯ; rands]

# make BigFloat big enough to hold floatmax() as an integer
setprecision(1024)

macro example(ex)
    ex isa Expr && ex.head == :tuple && length(ex.args) == 5 ||
        error("invalid @example call: $ex")
    map!(ex.args, ex.args) do arg
        arg isa AbstractString ? :(BigFloat($arg)) : esc(arg)
    end
    :(push!(examples, $ex))
end

examples = Tuple{BigInt,BigInt,BigInt,BigInt,Float64}[]

for x in shifts, a in [3, 1, -1, -3]
    @example a, 2, 19, 10, x
end

@example -1, 1, 0, 10, 0
@example -2, 1, 0, 10, 0
@example -3, 1, 0, 10, 0
@example -19, 1, 0, 10, 0
@example 0, 1, 1, 10, 0
@example 0, 1, 2, 10, 0
@example 0, 1, 3, 10, 0
@example 0, 1, 19, 10, 0
@example 0, 15, 42000, 100, 0

@example  "-3e50", "1e50", "4e50", 1, 0
@example  "-3e50", "1e50", "4e50", "1e25", 0
@example  "-3e50", "1e50", "4e50", "1e50", 0
@example  "-3e50", "1e50", "4e50", "1e60", 0

@example  "-1e20", "3", "2e20", 1, 0
@example  "-1e20", "3", "2e20", "1e10", 0
@example  "-1e20", "3", "2e20", "1e20", 0
@example  "-1e20", "3", "2e20", "1e30", 0

@example "-1e18", "3", "2e19", 1, 0
@example "-1e18", "3", "2e19", 10, 0
@example "-1e18", "3", "2e19", "1e9", 0
@example "-1e18", "3", "2e19", "1e17", 0
@example "-1e18", "3", "2e19", "1e18", 0
@example "-1e18", "3", "2e19", "1e19", 0
@example "-1e18", "3", "2e19", "1e20", 0

@example "-1e15", "9", "8e16", 1, 0
@example "-1e15", "9", "8e16", 10, 0
@example "-1e15", "9", "8e16", "1e5", 0
@example "-1e15", "9", "8e16", "1e10", 0
@example "-1e15", "9", "8e16", "1e14", 0
@example "-1e15", "9", "8e16", "1e15", 0
@example "-1e15", "9", "8e16", "1e16", 0
@example "-1e15", "9", "8e16", "1e17", 0

# subnormal ranges
@example -10, 5, 15, "1e324", 0
@example   0, 5, 15, "1e324", 0
@example -15, 5,  0, "1e324", 0

# TODO (broken):
# @example 3, 2, 19, "1e310", 0.0

@testset "tests" begin
    T = Float64
    for (A, S, B, D, x) in examples
        # @show (A, S, B, D, x)
        (a, s, b) = map(T, (A/D + x, S/D, B/D + x))
        r = lift_range(a, s, b)
        R = A:S:B
        l = length(R)
        @test r.n == l-1
        @test first(r) == a
        @test step(r) == s
        @test last(r) == b
        @test r[1] == a
        l ≤ typemax(Int) || continue
        @test length(r) == l
        @test r[l] == b
        i = searchsortedfirst(R, 0)
        for j = i-10:i+10
            1 ≤ j ≤ l || continue
            # comparison is exact at zero
            @test r[j] - T(R[j]/D) ≈ x
        end
    end
end
