function simplest_between(x::Rational{T}, y::Rational{T}) where {T<:Integer}
    x, y = minmax(x, y)
    y < 0 && return -simplest_between(-y, -x)
    x ≤ 0 && return zero(Rational{T})

    s = numerator(x)
    t = denominator(x)
    u = numerator(y)
    v = denominator(y)

    a = one(T)
    b = zero(T)
    c = zero(T)
    d = one(T)
    
    while true
        q = (s - one(T)) ÷ t
        s, t, u, v = v, u-q*v, t, s-q*t
        a, b, c, d = b+q*a, a, d+q*c, c
        s ≤ t && return (a + b)//(c + d)
    end
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
    a⁻ = max((A - eᴬ)//1, (B - eᴮ)*y)//big(2)^(-p+1)
    a⁺ = min((A + eᴬ)//1, (B + eᴮ)*y)//big(2)^(-p+1)
    â = simplest_between(a⁻, a⁺)
    b̂ = â/y
    ŝ = (b̂-â)/n
    return â, ŝ, b̂
end
