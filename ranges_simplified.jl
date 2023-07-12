# pick value in interval with the most trailing zeros
function tz_max(lo::T, hi::T) where {T<:Integer}
    lo == hi && return lo
    hi < 0 && return -tz_max(-hi, -lo)
    lo ≤ 0 && return 0
    @assert 0 < lo < hi
    e = exponent(hi - lo)
    b = hi >> e
    a = max(lo, (b - 1) << e)
    b <<= e
    m = trailing_zeros(a) ≥ trailing_zeros(b) ? a : b
    @assert lo ≤ m ≤ hi
    return m
end

function median3(a, b, c)
    b ≤ a ≤ c || c ≤ a ≤ b ? a :
    a ≤ b ≤ c || c ≤ b ≤ a ? b : c
end

function lift_range(a::Float64, s::Float64, b::Float64)
    A⁻ = prevfloat(a/2)
    A⁺ = nextfloat(a/2)
    B⁻ = prevfloat(b/2)
    B⁺ = nextfloat(b/2)
    S⁻ = prevfloat(s/2)
    S⁺ = nextfloat(s/2)

    s < 0 && ((S⁻, S⁺) = (S⁺, S⁻))
    p = q = r = 0
    while true
        r += 1
        p⁻ = Int64(div(r*A⁻, S⁺, RoundUp))
        p⁺ = Int64(div(r*A⁺, S⁻, RoundDown))
        p⁻ ≤ p⁺ || continue
        q⁻ = Int64(div(r*B⁻, S⁺, RoundUp))
        q⁺ = Int64(div(r*B⁺, S⁻, RoundDown))
        q⁻ ≤ q⁺ || continue
        p = tz_max(p⁻, p⁺)
        q = tz_max(q⁻, q⁺)
        break
    end
    s < 0 && ((S⁻, S⁺) = (S⁺, S⁻))

    g = median3(a/p, b/q, s/r)
    d⁺ = min((A⁺ - g*0.5p)/0.5p, (B⁺ - g*0.5q)/0.5q, (S⁺ - g*0.5r)/0.5r)
    d⁻ = max((A⁻ - g*0.5p)/0.5p, (B⁻ - g*0.5q)/0.5q, (S⁻ - g*0.5r)/0.5r)
    d = 0.5*((a - g*p)/p + (b - g*q)/q)
    @assert d⁻ ≤ d⁺
    d = 0.5*(d⁻ + d⁺)
    g, d = Base.canonicalize2(g, d)

    [g*i + d*i for i=p:r:q]
end
