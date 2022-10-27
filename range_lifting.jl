# based on https://stackoverflow.com/a/65189151/659248

using Base: TwicePrecision

# Intervals of TwicePrecisions

struct Interval{F<:AbstractFloat} <: Number
    lo::TwicePrecision{F}
    hi::TwicePrecision{F}
end
Interval(x::AbstractFloat) = Interval(mid(prevfloat(x), x), mid(x, nextfloat(x)))

Base.in(r::Union{Real,TwicePrecision}, V::Interval) = V.lo ≤ r ≤ V.hi

mid(a::Float64, b::Float64) = TwicePrecision(0.5a) + TwicePrecision(0.5b)
mid(V::Interval) = 0.5V.lo + 0.5V.hi

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
Base.:-(V::Interval, x::TwicePrecision) = typeof(V)(V.lo - x, V.hi - x)
Base.:*(x::Real, V::Interval) = typeof(V)(minmax(x*V.lo, x*V.hi)...)
Base.:*(x::TwicePrecision, V::Interval) = Interval(minmax(x*V.lo, x*V.hi)...)
Base.:/(V::Interval, x::TwicePrecision) = Interval(minmax(V.lo/x, V.hi/x)...)
Base.:/(x::TwicePrecision, V::Interval) = Interval(minmax(x/V.lo, x/V.hi)...)

Base.inv(U::Interval) = Interval(minmax(inv(U.lo), inv(U.hi))...)

ilog10(x::TwicePrecision) = Int(floor(log10(x.hi))) # TODO: approximate

Base.isinteger(x::TwicePrecision) = isinteger(x.lo) & isinteger(x.hi)

function shrink_int(V::Interval)
    lo = round(V.lo, RoundUp)
    hi = round(V.hi, RoundDown)
    lo ≤ hi && return Interval(lo, hi)
    r = round(0.5V.lo + 0.5V.hi)
    return Interval(r, r)
end

# pick value in interval with the most trailing zeros
function pick_max_tz(V::Interval{F}) where {F<:AbstractFloat}
    lo, hi = V.lo, V.hi
    lo == hi && return lo
    𝟘 = zero(lo)
    hi < 𝟘 && return -pick_max_tz(-V)
    lo ≤ 𝟘 && return 𝟘
    @assert 𝟘 < lo < hi
    e = exponent(hi - lo)
    a = round(lo*exp2(-e), RoundUp)
    b = round(hi*exp2(-e), RoundDown)
    @assert a ≤ b ≤ a + 1
    c = tz(a) ≥ tz(b) ? a : b
    n = c*exp2(e)
    @assert lo ≤ n ≤ hi
    return n
end

function ratio(x::TwicePrecision{<:AbstractFloat})
    d = inv(iszero(x.lo) ? eps(x.hi) : eps(x.lo))
    return x*d, TwicePrecision(d)
end

# exact modulus of an integer-valued TwicePrecision 
function Base.:%(x::TwicePrecision{F}, S::Type{<:Signed}) where {F<:Base.IEEEFloat}
    (Signed(x.hi/eps(x.hi)) % S) << exponent(eps(x.hi)) +
    (Signed(x.lo/eps(x.lo)) % S) << exponent(eps(x.lo))
end

# how many powers of two divide an integer-valued TwicePrecision
tz(x::TwicePrecision) = trailing_zeros(x % Int128)

# more accurate ring operations on integer-valued TwicePrecision
function int_op(op::Function, x::TwicePrecision, y::TwicePrecision)
    z = op(x, y)
    z += op(x % Signed, y % Signed) - (z % Signed)
end

# +̇(x::TwicePrecision, y::TwicePrecision) = int_op(+, x, y)
# -̇(x::TwicePrecision, y::TwicePrecision) = int_op(-, x, y)
# *̇(x::TwicePrecision, y::TwicePrecision) = int_op(*, x, y)

function simplest_rational(V::Interval)
    𝟘, 𝟙 = zero(V.lo), one(V.lo)

    # reduce to positive case
    if V.hi < 𝟘
        N, D = simplest_rational(-V)
        return -N, D
    end

    # check if V or 1/V contain integers
    N = pick_max_tz(V)
    isinteger(N) && return N, 𝟙
    Λ = inv(V)
    D = pick_max_tz(Λ)
    isinteger(D) && return 𝟙, D

    N₁, D₁ = simplest_rational_core(V)
    D₂, N₂ = simplest_rational_core(Λ)

    tz(N₁) + tz(D₁) ≥ tz(N₂) + tz(D₂) ? (N₁, D₁) : (N₂, D₂)
end

function simplest_rational_core(V::Interval)
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
    N = pick_max_tz(D*V)
    D = pick_max_tz(N/V)

    return N, D
end

function continued_fraction(V::Interval)
    x, y = ratio(mid(V))
    T = typeof(x)
    R = Tuple{T,T}[]
    𝟘, 𝟙 = zero(T), one(T)
    a = d = 𝟙
    b = c = 𝟘
    interior = false
    while y ≠ 𝟘
        q, r = divrem(x, y)
        a, b, c, d = q*a + b, a, q*̇c + d, c
        ab, cd = a + b, c + d
        interior = interior || ab/cd ∈ V
        interior && push!(R, (ab, cd))
        x, y = y, r
    end
    return R
end

Base.zero(x::TwicePrecision) = zero(typeof(x))
Base.one(x::TwicePrecision) = one(typeof(x))
Base.one(T::Type{<:TwicePrecision}) = T(1, 0)

Base.copy(x::TwicePrecision) = x

function Base.:(==)(x::TwicePrecision, y::TwicePrecision)
    d = x - y
    iszero(d.hi) && iszero(d.lo)
end

function Base.round(
    x::TwicePrecision{<:AbstractFloat},
    R::RoundingMode{mode} = RoundNearest,
) where {mode}
    if eps(x.hi) ≥ 1
        flip = mode in (:ToZero, :FromZero) && x.hi*x.lo < 0
        r_lo = flip ? -round(-x.lo, R) : round(x.lo, R)
        return TwicePrecision(x.hi, r_lo)
    else
        next = nextfloat(x.hi, Int(sign(x.lo)))
        this = round(x.hi, R)
        that = round(next, R)
        this == that && return TwicePrecision(this)
        edge = mode in (:ToZero, :FromZero, :Up, :Down) ? 0.0 : 0.5
        frac = abs(x.hi - this)
        return TwicePrecision(frac == edge ? that : this)
    end
end

function Base.div(
    a::TwicePrecision{T},
    b::TwicePrecision{T},
    R::RoundingMode,
) where {T}
    round(a/b, R)
end

function Base.divrem(a::TwicePrecision, b::TwicePrecision, R::RoundingMode)
    q = div(a, b, R)
    q, a - q*̇b
end

Base.inv(x::TwicePrecision) = one(typeof(x))/x
Base.abs(x::TwicePrecision) = signbit(x.hi) ? -x : x
Base.isnan(x::TwicePrecision) = isnan(x.hi) | isnan(x.lo)
Base.isless(x::TwicePrecision, y::TwicePrecision) = x < y
Base.exponent(x::TwicePrecision) = exponent(x.hi)

int(x::TwicePrecision) = BigInt(x.hi) + BigInt(x.lo)

Base.bitstring(n::BigInt) = string(n, base=2)

function lift_range(a::Float64, s::Float64, b::Float64)
    T = TwicePrecision{Float64}
    𝟘, 𝟙 = zero(T), one(T)

    A = Interval(a)
    S = Interval(s)
    B = Interval(b)

    X = A/S
    Y = B/S
    x = pick_max_tz(X)
    y = pick_max_tz(Y)

    if isinteger(x) && isinteger(y)
        # offset is exactly zero
        ff = 𝟘, 𝟙
    else
        isinteger(x) || (x = round(X.lo, RoundDown))
        isinteger(y) || (y = round(Y.lo, RoundDown))
        F = (X - x) & (Y - y)
        @assert 𝟘 < F.lo < F.hi < 𝟙
        # infeasible if this interval is empty
        ff = simplest_rational_core(F)
        f = /(ff...)
        x += f
        y += f
    end

    # find a nice rational step
    S &= A/x
    S &= B/y
    ss = simplest_rational(S)
    ŝ = /(ss...)

    # compute offsets & length
    q = round(x, RoundDown)
    z = /((ff .* ss)...)
    n = y - x

    # range computation
    rg(k) = z + (k + q)*ŝ
    [rg(k) for k = 0:Int(n)]
end
