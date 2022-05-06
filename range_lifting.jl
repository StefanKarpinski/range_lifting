# based on https://stackoverflow.com/a/65189151/659248

function simplest_between(s::R, t::R, u::R, v::R) where {R<:Real}
    if u*t < s*v
        s, u = u, s
        t, v = v, t
    end
    if u*v < 0
        n, d = simplest_between(-u, v, -s, t)
        return -n, d
    end
    if s*t ≤ 0
        return zero(R), one(R)
    end

    a = d = one(R)
    b = c = zero(R)

    while true
        q = (s - one(R)) ÷ t
        s, t, u, v = v, u-q*v, t, s-q*t
        a, b, c, d = b+q*a, a, d+q*c, c
        s ≤ t && return a+b, c+d
    end
end

function simplest_between(x::Rational, y::Rational)
    Rational(simplest_between(
        numerator(x), denominator(x),
        numerator(y), denominator(y),
    )...)
end

function lift_range(a::Float64, s::Float64, b::Float64)
    n = round(Int, (b - a)/s)
    q = round(Int, (1 + (a + b)/(a - b))*(n/2))
    A, pᴬ, σᴬ = Base.decompose(a); A *= σᴬ
    B, pᴮ, σᴮ = Base.decompose(b); B *= σᴮ
    p = min(pᴬ, pᴮ)
    A <<= 1 + pᴬ - p
    B <<= 1 + pᴮ - p
    eᴬ = 1 << (pᴬ - p)
    eᴮ = 1 << (pᴮ - p)
    # check that 0 ∉ (A - B) ± (eᴬ + eᴮ)
    # (otherwise interior extrema can occur)
    # (can only happen with unequal subnormals)
    R⁻ = R⁺ = (A + B)//(A - B)
    for dᴬ in (-eᴬ, eᴬ), dᴮ in (-eᴮ, eᴮ)
        R = ((A + dᴬ) + (B + dᴮ))//((A + dᴬ) - (B + dᴮ))
        R < R⁻ && (R⁻ = R)
        R > R⁺ && (R⁺ = R)
    end
    r⁻ = n*(1 + R⁻)/2 - q
    r⁺ = n*(1 + R⁺)/2 - q
    r = simplest_between(r⁻, r⁺)
    x = r + q
    y = x/(x-n)
    A⁻ = max((A - eᴬ)//1, (B - eᴮ)*y)
    A⁺ = min((A + eᴬ)//1, (B + eᴮ)*y)
    â_n, â_d = simplest_between(
        numerator(A⁻)*1.0, denominator(A⁻)*exp2(-p+1),
        numerator(A⁺)*1.0, denominator(A⁺)*exp2(-p+1),
    )
    â = Int(â_n)//Int(â_d)
    b̂ = â/y
    ŝ = (b̂-â)/n
    return â, ŝ, b̂
end
