# based on https://stackoverflow.com/a/65189151/659248

using Base: TwicePrecision

function ratio(x::TwicePrecision{<:AbstractFloat})
    d = inv(iszero(x.lo) ? eps(x.hi) : eps(x.lo))
    return x*d, TwicePrecision(d)
end

# exact 2^(8*sizeof(F)) modulus of an integer-valued TwicePrecision
function Base.:%(x::TwicePrecision{F}, Signed) where {F<:Base.IEEEFloat}
    Signed(x.hi/eps(x.hi)) << exponent(eps(x.hi)) +
    Signed(x.lo/eps(x.lo)) << exponent(eps(x.lo))
end

# how many powers of two divide an integer-valued TwicePrecision
tz(x::TwicePrecision) = trailing_zeros(x % Signed)

# more accurate ring operations on integer-valued TwicePrecision
function int_op(op::Function, x::TwicePrecision, y::TwicePrecision)
    z = op(x, y)
    z += op(x % Signed, y % Signed) - (z % Signed)
end

+̇(x::TwicePrecision, y::TwicePrecision) = int_op(+, x, y)
-̇(x::TwicePrecision, y::TwicePrecision) = int_op(-, x, y)
*̇(x::TwicePrecision, y::TwicePrecision) = int_op(*, x, y)

function simplest_rational(V::Interval{F})
    𝟘, 𝟙 = zero(V.lo), one(V.lo)
    if y < 𝟘
        N, D = simplest_rational(-V)
        return -N, D
    end
    N = pick_int(V)
    !isnan(N) && return N, 𝟙
    Λ = inv(V)
    D = pick_int(Λ)
    !isnan(D) && return 𝟙, D

    N₁, D₁ = simplest_rational_core(V)
    D₂, N₂ = simplest_rational_core(Λ)

    if D₂ < 𝟘
        N₂ = -N₂
        D₂ = abs(D₂)
    end

    g₁ = tz(N₁) + tz(D₁)
    g₂ = tz(N₂) + tz(D₂)

    g₁ > g₂ && return N₁, D₁
    g₁ < g₂ && return N₂, D₂

    g₁ = abs(N₁) + D₁
    g₂ = abs(N₂) + D₂

    g₁ ≥ g₂ ? (N₁, D₁) : (N₂, D₂)
end

function simplest_rational_core(V::Interval{F})
    𝟘, 𝟙 = zero(V.lo), one(V.lo)

    s, t = ratio(V.lo)
    u, v = ratio(V.hi)

    a = d = 𝟙
    b = c = 𝟘

    while true
        q = s ÷ t
        s, t, u, v = v, u-q*v, t, s-q*t
        a, b, c, d = b+q*a, a, d+q*c, c
        s < t && break
    end

    N, D = a + b, c + d
    N = pick_int(D*V)
    D = pick_int(N/V)

    return N, D
end

Base.zero(x::TwicePrecision) = zero(typeof(x))
Base.one(x::TwicePrecision) = one(typeof(x))
Base.one(T::Type{<:TwicePrecision}) = T(1, 0)

Base.copy(x::TwicePrecision) = x

function Base.round(
    x::TwicePrecision{<:AbstractFloat},
    r::RoundingMode{mode} = RoundNearest,
) where {mode}
    if eps(x.hi) ≥ 1
        flip = mode in (:ToZero, :FromZero) && x.hi*x.lo < 0
        r_lo = flip ? -round(-x.lo, r) : round(x.lo, r)
        return TwicePrecision(x.hi, r_lo)
    else
        next = nextfloat(x.hi, Int(sign(x.lo)))
        this = round(x.hi, r)
        that = round(next, r)
        this == that && return TwicePrecision(this)
        edge = mode in (:ToZero, :FromZero, :Up, :Down) ? 0.0 : 0.5
        frac = abs(x.hi - this)
        return TwicePrecision(frac == edge ? that : this)
    end
end

function Base.div(
    a::TwicePrecision{T},
    b::TwicePrecision{T},
    r::RoundingMode,
) where {T}
    round(a/b, r)
end

Base.inv(x::TwicePrecision) = one(typeof(x))/x
Base.abs(x::TwicePrecision) = signbit(x.hi) ? -x : x
Base.isnan(x::TwicePrecision) = isnan(x.hi) | isnan(x.lo)
Base.isless(x::TwicePrecision, y::TwicePrecision) = x < y
Base.bitstring(n::BigInt) = string(n, base=2)

int(x::TwicePrecision) = BigInt(x.hi) + BigInt(x.lo)

mid(a::Float64, b::Float64) = TwicePrecision(0.5a) + TwicePrecision(0.5b)

struct Interval{F<:AbstractFloat} <: Number
    lo::TwicePrecision{F}
    hi::TwicePrecision{F}
end
Interval(x::AbstractFloat) = Interval(mid(prevfloat(x), x), mid(x, nextfloat(x)))

# TODO: maybe unroll/optimize this
@inline lo_hi(op::Function, U::Interval, V::Interval) =
    extrema((op(U.lo, V.lo), op(U.lo, V.hi), op(U.hi, V.lo), op(U.hi, V.hi)))

Base.:-(U::Interval) = Interval(-U.hi, -U.lo)
Base.:+(U::Interval, V::Interval) = Interval(U.lo + V.lo, U.hi + V.hi)
Base.:-(U::Interval, V::Interval) = Interval(U.lo - V.hi, U.hi - V.lo)
Base.:*(U::Interval, V::Interval) = Interval(lo_hi(*, U, V)...)
Base.:/(U::Interval, V::Interval) = Interval(lo_hi(/, U, V)...)
Base.:&(U::Interval, V::Interval) = Interval(max(U.lo, V.lo), min(U.hi, V.hi))

Base.:+(x::Real, V::Interval) = typeof(V)(x + V.lo, x + V.hi)
Base.:*(x::Real, V::Interval) = typeof(V)(minmax(x*V.lo, x*V.hi)...)
Base.:*(x::TwicePrecision, V::Interval) = Interval(minmax(x*V.lo, x*V.hi)...)
Base.:/(V::Interval, x::TwicePrecision) = Interval(minmax(V.lo/x, V.hi/x)...)

Base.inv(U::Interval) = Interval(minmax(inv(U.lo), inv(U.hi))...)

simplest_rational(V::Interval) = simplest_rational(V.lo, V.hi)

ilog10(x::TwicePrecision) = Int(floor(log10(x.hi))) # TODO: approximate

# pick integer in the interval with the most trailing zeros
function pick_int(V::Interval{F}) where {F<:AbstractFloat}
    𝟘 = zero(V.lo)
    V.hi < 𝟘 && return -pick_int(-V)
    V.lo ≤ 𝟘 && return 𝟘
    lo = round(V.lo, RoundUp)
    hi = round(V.hi, RoundDown)
    lo > hi && return oftype(lo, NaN)
    lo < hi || return lo
    @assert 𝟘 < lo < hi

    # find range of at most 10 good candidates
    l = ilog10(hi -̇ lo)
    m = Int(floor(log(5, maxintfloat(F))))
    q, r = divrem(l, m)
    p = Base.power_by_squaring(TwicePrecision(F(10)^m), q)
    p *= F(10)^r
    n = round(lo/p, RoundUp)
    h = round(hi/p, RoundDown)

    # pick the one with the most factors of two
    n′ = n
    g = tz(n′)
    while (n′ += 1) ≤ h
        (g′ = tz(n′)) > g || continue
        g, n = g′, n′
    end

    # remultiply by p
    n *= p
    @assert lo ≤ n ≤ hi
    return n
end

function lift_range(a::Float64, s::Float64, b::Float64)
    A = Interval(a)
    S = Interval(s)
    B = Interval(b)

    X = A/S
    Y = B/S
    x = pick_int(X)
    y = pick_int(Y)

    # TODO: handle case where S is integral

    if !isnan(x) && !isnan(y) # x & y are integers
        # tighten bounds on S, A, B
        S &= A/x
        S &= B/y
        N, D = simplest_rational(S)
        q = x # already an integer
        z = zero(q)
        ŝ = N/D
    else # x & y are non-integers
        N = (B - A)/S
        n = pick_int(N)
        isnan(n) && error("infeasible range")
        
    end

    n = pick_int((B - A)/S)
    R = (A + B)/(A - B)
    Q = -0.5n*(1 + R)

    # want simple f such that a - (q + f)*s == 0
    #   where q ∈ ℤ and |f| ≤ 1/2
    h = -0.5n
    q = round(-0.5n*(1 + R))
    f⁻ = h*(1 + r⁺) - q
    f⁺ = h*(1 + r⁻) - q
    # define x = a/s, y = b/s
    # f = F/d, x = X/d, y = Y/d
    F, d = simplest_rational(f⁻, f⁺)
    X = F + q*d # x = f + q = (F + q*d)/d
    Y = X + n*d # y = x + n = (X + n*d)/d

    # tighten bounds on `s`
    # s = a/x = a/(X/d) = a*d/X
    s⁻′, s⁺′ = minmax(a⁻*d/X, a⁺*d/X)
    s⁻ = max(s⁻, s⁻′)
    s⁺ = min(s⁺, s⁺′)
    # s = b/y = b/(Y/d) = b*d/Y
    s⁻′, s⁺′ = minmax(b⁻*d/Y, b⁺*d/Y)
    s⁻ = max(s⁻, s⁻′)
    s⁺ = min(s⁺, s⁺′)

    # simplest rational for `s`
    S, D = simplest_rational(s⁻, s⁺)

    # compute the zero point and step
    z = (F*S)/(D*d)
    ŝ = S/D

    rg(k) = z + (k +̇ q)*ŝ
    [rg(k) for k = 0:Int(n)]
end
