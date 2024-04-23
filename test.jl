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

for x in shifts[1:4], a in [3, 1, -1, -3]
    @example a, 2, 19, 10, x
end

@example "-3e50", "1e50", "4e50", 1, 0
@example "-1e20", 3, "2e20", 1, 0
@example "-1e18", 3, "2e19", 10, 0
@example "-1e15", 9, "8e16", 10, 0

for (A, S, B, D, x) in examples
    global a, s, b, r, N
    @show A, S, B, D, x
    (a, s, b) = map(Float64, (A/D + x, S/D, B/D + x))
    @show (a, s, b)
    try
        r = lift_range(a, s, b)
    catch err
        show(err)
        println()
    end
end
