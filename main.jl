import Base: TwicePrecision, canonicalize2, add12, div12, mul12

Base.isless(x::TwicePrecision, y::TwicePrecision) =
    isless(x.hi, y.hi) || isequal(x.hi, y.hi) && isless(x.lo, y.lo)
Base.:(<=)(x::TwicePrecision, y::TwicePrecision) =
    x.hi < y.hi || x.hi == y.hi && x.lo <= y.lo
Base.:(<)(x::TwicePrecision, y::TwicePrecision) =
    x.hi < y.hi || x.hi == y.hi && x.lo < y.lo

Base.zero(x::TwicePrecision) = typeof(x)(zero(x.hi))
Base.one(x::TwicePrecision) = typeof(x)(one(x.hi))

Base.inv(x::TwicePrecision) = one(x)/x
Base.signbit(x::TwicePrecision) = iszero(x.hi) ? signbit(x.lo) : signbit(x.hi)
Base.isinteger(x::TwicePrecision) = isinteger(x.hi) & isinteger(x.lo)

Base.floatmax(x::TwicePrecision{T}) where {T<:AbstractFloat} =
    TwicePrecision(floatmax(T), ldexp(floatmax(T), -precision(T)-1))

function Base.nextfloat(x::TwicePrecision)
    lo = nextfloat(x.lo)
    x.hi + lo == x.hi && return TwicePrecision(x.hi, lo)
    y = TwicePrecision(canonicalize2(x.hi, lo)...)
    lo = prevfloat(y.lo)
    y.hi + lo == y.hi && return TwicePrecision(y.hi, lo)
    return y
end

function Base.prevfloat(x::TwicePrecision)
    lo = prevfloat(x.lo)
    x.hi + lo == x.hi && return TwicePrecision(x.hi, lo)
    y = TwicePrecision(canonicalize2(x.hi, lo)...)
    lo = nextfloat(y.lo)
    y.hi + lo == y.hi && return TwicePrecision(y.hi, lo)
    return y
end

# more accurate twice precision addition
# based on "Bailey’s QD library": https://www.davidhbailey.com/dhbsoftware/
# via https://mycourses.aalto.fi/pluginfile.php/926578/mod_resource/content/1/9781489979810-c2.pdf (Algorithm 6)
function Base.:(+)(x::TwicePrecision{T}, y::TwicePrecision{T}) where T
    s_hi, s_lo = add12(x.hi, y.hi)
    t_hi, t_lo = add12(x.lo, y.lo)
    c = s_lo + t_hi
    v_hi, v_lo = canonicalize2(s_hi, c)
    w = t_lo + v_lo
    TwicePrecision(canonicalize2(v_hi, w)...)
end

# more accurate twice precision division
# based on "Bailey’s QD library": https://www.davidhbailey.com/dhbsoftware/
function Base.:(/)(x::TwicePrecision{T}, y::TwicePrecision{T}) where T
    q1 = x.hi/y.hi
    r = x - q1*y
    q2 = r.hi/y.hi
    r -= q2*y
    q3 = r.hi/y.hi
    TwicePrecision(canonicalize2(q1, q2)...) + TwicePrecision(q3)
end

Base.:(/)(x::T, y::TwicePrecision{T}) where T = TwicePrecision(x)/y

normalize⁺(x::AbstractFloat) =
    !issubnormal(x) ? x : signbit(x) ? -zero(x) : floatmin(x)
normalize⁻(x::AbstractFloat) =
    !issubnormal(x) ? x : signbit(x) ? -floatmin(x) : zero(x)

normalize⁺(x::TwicePrecision{T}) where {T<:AbstractFloat} =
    issubnormal(x.hi) ? TwicePrecision(normalize⁺(x.hi)) :
    issubnormal(x.lo) ?
        TwicePrecision(canonicalize2(x.hi, normalize⁺(x.lo))...) : x
normalize⁻(x::TwicePrecision{T}) where {T<:AbstractFloat} =
    issubnormal(x.hi) ? TwicePrecision(normalize⁻(x.hi)) :
    issubnormal(x.lo) ?
        TwicePrecision(canonicalize2(x.hi, normalize⁻(x.lo))...) : x

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
) where {T<:AbstractFloat}
    round(a/b, R)
end

tmul(x::T, y::TwicePrecision{T}) where {T<:AbstractFloat} =
    fma(x, y.hi, x*y.lo)

function tz(x::T) where {T<:AbstractFloat}
    iszero(x) && return typemax(Int)
    n, p = Base.decompose(x)
    trailing_zeros(n) + p
end

tz(n::Integer) = trailing_zeros(n)
tz(x::TwicePrecision) = iszero(x.lo) ? tz(x.hi) : tz(x.lo)

# pick the value in the interval with the fewest significant bits, i.e. the
# smallest span from leading to trailing set bit; ties broken toward smaller
# magnitude. Within a single binade the leading bit is fixed, so this reduces
# to "most trailing zeros". Across binades the interval contains a power of two
# (one significant bit), and we take the smallest such — accounting for the
# leading-bit ("max digit") term that most-trailing-zeros alone ignores.
function simplest_float(lo::T, hi::T) where {T<:AbstractFloat}
    lo == hi && return lo
    hi < 0 && return -simplest_float(-hi, -lo)
    lo ≤ 0 && return zero(T)
    @assert 0 < lo < hi
    # smallest power of two ≥ lo; if it's in range it's the fewest-significant-
    # bits (= 1) value, and the smallest such, so it wins outright
    p = ldexp(one(T), exponent(lo))     # largest power of two ≤ lo
    p < lo && (p *= 2)                   # smallest power of two ≥ lo
    p ≤ hi && return p
    # otherwise [lo, hi] lies within one binade: fewest significant bits ⟺ most
    # trailing zeros, and the max-tz value is unique
    e = exponent(hi - lo)
    b = floor(ldexp(hi, -e))
    a = max(lo, ldexp(b - 1, e))
    b = ldexp(b, e)
    m = tz(a) ≥ tz(b) ? a : b
    @assert lo ≤ m ≤ hi
    return m
end

function simplest_float(
    lo :: TwicePrecision{T},
    hi :: TwicePrecision{T},
) where {T<:AbstractFloat}
    lo.hi == hi.hi &&
        return TwicePrecision(lo.hi, simplest_float(lo.lo, hi.lo))
    @assert lo.hi < hi.hi
    l = lo.lo ≤ 0 ? lo.hi : nextfloat(lo.hi)
    h = hi.lo ≥ 0 ? hi.hi : prevfloat(hi.hi)
    l ≤ h && return TwicePrecision(simplest_float(l, h))
    @assert 0 < lo.lo && hi.lo < 0
    lo.hi + simplest_float(TwicePrecision(lo.lo), hi - lo.hi)
end

# TODO: harden against overflow
function ratio(x::TwicePrecision{T}) where {T<:AbstractFloat}
    p = min(0, tz(x))
    n = TwicePrecision(ldexp(x.hi, -p), ldexp(x.lo, -p))
    d = TwicePrecision(exp2(-p))
    return n, d
end

# based on https://stackoverflow.com/a/65189151/659248 (inclusive version)
function simplest_rational_core(
    lo :: TwicePrecision{T},
    hi :: TwicePrecision{T},
) where {T<:AbstractFloat}
    𝟘 = zero(lo)
    𝟙 = one(lo)

    @assert 𝟘 < lo ≤ hi

    s, t = ratio(normalize⁺(lo))
    u, v = ratio(normalize⁻(hi))

    a = d = 𝟙
    b = c = 𝟘

    while true
        q = (s - 𝟙) ÷ t
        s, t, u, v = v, u-q*v, t, s-q*t
        a, b, c, d = b+q*a, a, d+q*c, c
        s ≤ t && break
    end

    return a + b, c + d
end

function simplest_rational(
    lo :: TwicePrecision{T},
    hi :: TwicePrecision{T},
) where {T<:AbstractFloat}
    𝟘 = zero(lo)
    𝟙 = one(lo)

    # reduce to positive case
    if hi < 𝟘
        n, d = simplest_rational(-hi, -lo)
        return -n, d
    end
    lo ≤ 𝟘 && return 0, 𝟙

    # if there are integers, return the simplest one
    if round(lo, RoundUp) ≤ round(hi, RoundDown)
        return simplest_float(lo, hi), 𝟙
    end

    # find strictly minimal solution
    n, d = simplest_rational_core(lo, hi)

    # simplify numerator and denominator
    n = simplest_float(d*lo, d*hi)
    d = simplest_float(n/hi, n/lo)

    # eliminate common factors of two
    z = min(tz(n), tz(d))
    n *= exp2(-z)
    d *= exp2(-z)

    # check we're in the interval
    @assert lo ≤ n/d ≤ hi
    return n, d
end

function smallest_denominator(
    lo :: TwicePrecision{T},
    hi :: TwicePrecision{T},
) where {T<:AbstractFloat}
    𝟘 = zero(lo)
    𝟙 = one(lo)

    # return one if the interval contains integers
    round(lo, RoundUp) ≤ round(hi, RoundDown) && return 𝟙

    # reduce to positive case
    if hi < 𝟘
        lo, hi = -hi, -lo
    end
    lo ≤ 𝟘 && return 𝟙

    # find strictly minimal solution
    n, d = simplest_rational_core(lo, hi)

    return d
end

function trunc_ival(
    lo :: TwicePrecision{T},
    hi :: TwicePrecision{T},
) where {T<:AbstractFloat}
    fl = floor(lo)
    lo - fl, hi - fl
end

function smallest_denominator(
    (a⁻, a⁺) :: NTuple{2,TwicePrecision{T}},
    (b⁻, b⁺) :: NTuple{2,TwicePrecision{T}},
    (c⁻, c⁺) :: NTuple{2,TwicePrecision{T}},
) where {T<:AbstractFloat}
    @show (a⁻, a⁺) (b⁻, b⁺) (c⁻, c⁺)
    # a⁻, a⁺ = trunc_ival(a⁻, a⁺)
    # b⁻, b⁺ = trunc_ival(b⁻, b⁺)
    # c⁻, c⁺ = trunc_ival(c⁻, c⁺)
    D = max(
        smallest_denominator(a⁻, a⁺),
        smallest_denominator(b⁻, b⁺),
        smallest_denominator(c⁻, c⁺),
    )
    while true
        A = round(D*a⁻, RoundUp)
        B = round(D*b⁻, RoundUp)
        C = round(D*c⁻, RoundUp)
        A ≤ D*a⁺ && B ≤ D*b⁺ && C ≤ D*c⁺ && break
        D = max(cld(A, a⁺), cld(B, b⁺), cld(C, c⁺))
    end
    D = T(D)
end

function ival(x::T) where {T<:AbstractFloat}
    lo = (TwicePrecision(x) + TwicePrecision(prevfloat(x)))/2
    hi = (TwicePrecision(x) + TwicePrecision(nextfloat(x)))/2
    return lo, hi
end

"""
    ratio_break⁺(x, y) -> r

Return a `TwicePrecision` value `r` such that:

    - `oftype(x, y*r) == x`
    - `oftype(x, y*nextfloat(r)) != x`

Inputs can be floats or `TwicePrecision` floats.
"""
function ratio_break⁺(
    x :: TwicePrecision{T},
    y :: TwicePrecision{T},
) where {T<:AbstractFloat}
    if signbit(y)
        x, y = -x, -y
    end
    iszero(y) && return floatmax(x)
    iszero(x) && return x
    r = x/y
    if r*y ≤ x
        r⁻ = r
        r⁺ = max(nextfloat(r), TwicePrecision(nextfloat(x.hi))/y)
    else
        r⁻ = min(prevfloat(r), TwicePrecision(prevfloat(x.hi))/y)
        r⁺ = r
    end
    @assert r⁻*y ≤ x < r⁺*y
    while true
        r = (r⁻ + r⁺)/2
        r⁻ < r < r⁺ || break
        x′ = r*y
        if x′ ≤ x
            r⁻ = r
        else
            r⁺ = r
        end
    end
    r = r⁻
    while y*r ≤ x
        r = nextfloat(r)
    end
    r = prevfloat(r)
    @assert y*r ≤ x
    @assert y*nextfloat(r) > x
    return r
end

function ratio_break⁺(x::T, y::Union{T,TwicePrecision{T}}) where T
    if signbit(y)
        x, y = -x, -y
    end
    # find largest double precision x⁺ such that T(x⁺) == x
    x⁺ = (TwicePrecision(x) + TwicePrecision(nextfloat(x)))/2
    T(x⁺) ≠ x && (x⁺ = prevfloat(x⁺))
    @assert T(x⁺) == x
    @assert T(nextfloat(x⁺)) == nextfloat(x)
    r = ratio_break⁺(x⁺, convert(TwicePrecision{T}, y))
    @assert iszero(y) || T(y*r) == x
    @assert T(y*nextfloat(r)) != x
    return r
end

"""
    ratio_break⁻(x, y) -> r

Return a `TwicePrecision` value `r` such that:

    - `oftype(x, y*r) == x`
    - `oftype(x, y*prevfloat(r)) != x`

Inputs can be floats or `TwicePrecision` floats.
"""
function ratio_break⁻(
    x::TwicePrecision{T},
    y::TwicePrecision{T},
) where {T<:AbstractFloat}
    if signbit(y)
        x, y = -x, -y
    end
    iszero(y) && return -floatmax(x)
    iszero(x) && return x
    r = x/y
    if r*y < x
        r⁻ = r
        r⁺ = max(nextfloat(r), TwicePrecision(nextfloat(x.hi))/y)
    else
        r⁻ = min(prevfloat(r), TwicePrecision(prevfloat(x.hi))/y)
        r⁺ = r
    end
    @assert r⁻*y < x ≤ r⁺*y
    while true
        r = (r⁻ + r⁺)/2
        r⁻ < r < r⁺ || break
        x′ = r*y
        if x′ < x
            r⁻ = r
        else
            r⁺ = r
        end
    end
    r = r⁺
    while y*r ≥ x
        r = prevfloat(r)
    end
    r = nextfloat(r)
    @assert y*r ≥ x
    @assert y*prevfloat(r) < x
    return r
end

function ratio_break⁻(x::T, y::Union{T,TwicePrecision{T}}) where T
    if signbit(y)
        x, y = -x, -y
    end
    # find smallest double precision x⁻ such that T(x⁻) == x
    x⁻ = (TwicePrecision(x) + TwicePrecision(prevfloat(x)))/2
    T(x⁻) ≠ x && (x⁻ = nextfloat(x⁻))
    @assert T(x⁻) == x
    @assert T(prevfloat(x⁻)) == prevfloat(x)
    r = ratio_break⁻(x⁻, convert(TwicePrecision{T}, y))
    @assert iszero(y) || T(y*r) == x
    @assert T(y*prevfloat(r)) != x
    return r
end

"""
    ratio_ival(x, y)

Shorthand for `ratio_break⁻(x, y), ratio_break⁺(x, y)`.
"""
function ratio_ival(x::T, y::T) where {T<:AbstractFloat}
    ratio_break⁻(x, y), ratio_break⁺(x, y)
end

struct FRange{T<:AbstractFloat} <: AbstractRange{T}
    A::T
    S::T
    n::T
    g::TwicePrecision{T}
end

Base.length(r::FRange) = max(0, Int(r.n) + 1)
Base.first(r::FRange) = r[1]
Base.step(r::FRange) = tmul(r.S, r.g)
Base.last(r::FRange) = getindex0(r, r.n)
Base.getindex(r::FRange, i::Integer) = getindex0(r, i-1)

getindex0(r::FRange{T}, i::Real) where {T<:AbstractFloat} =
    T((r.A + convert(TwicePrecision{T}, i)*r.S)*r.g)

macro sign_swap(syms::Symbol...)
    blk = quote end
    for s in syms
        s⁻ = esc(Symbol("$(s)⁻"))
        s⁺ = esc(Symbol("$(s)⁺"))
        s = esc(s)
        push!(blk.args, :(
            if signbit($s)
                $s⁻, $s⁺ = -$s⁺, -$s⁻
            end
        ))
    end
    blk
end

macro update(cmp::Expr, body::Expr=quote end)
    cmp.head == :call &&
    length(cmp.args) == 3 &&
    cmp.args[1] in (:<, :>) &&
    cmp.args[2] isa Symbol
    lt = esc(cmp.args[1])
    var = esc(cmp.args[2])
    val = esc(cmp.args[3])
    quote
        val = $val
        if $lt($var, val)
            $var = val
            $(esc(body))
            $(esc(:changed)) = true
        end
    end
end

lcmf(args::T...) where {T<:AbstractFloat} =
    T(lcm(map(Int64, args)...))
gcdf(args::T...) where {T<:AbstractFloat} =
    T(gcd(map(Int64, args)...))

function lift_range(a::T, s::T, b::T) where {T<:AbstractFloat}
    # handle negative step
    if signbit(s)
        a = -a
        b = -b
        s = -s
    end
    @show a, b, s
    # double precision intervals for a, b, s
    a⁻, a⁺ = ival(a)
    b⁻, b⁺ = ival(b)
    s⁻, s⁺ = ival(s)
    # end-point/step ratio intervals
    r_a⁻ = ratio_break⁻(a⁻, signbit(a) ? s⁻ : s⁺)
    r_a⁺ = ratio_break⁺(a⁺, signbit(a) ? s⁺ : s⁻)
    r_b⁻ = ratio_break⁻(b⁻, signbit(b) ? s⁻ : s⁺)
    r_b⁺ = ratio_break⁺(b⁺, signbit(b) ? s⁺ : s⁻)
    # pick simplest range length
    N = T(simplest_float(r_b⁻ - r_a⁺, r_b⁺ - r_a⁻))
    # check if end-point can be hit
    p = tz(N)
    p ≥ 0 || error("end-point can't be hit (length)")
    # scaled down intervals
    if p > 0
        a⁻, a⁺ = ival(ldexp(a, -p))
        b⁻, b⁺ = ival(ldexp(b, -p))
    end
    # rationalize the three intervals
    D = smallest_denominator((a⁻, a⁺), (b⁻, b⁺), (s⁻, s⁺))
    A = T(simplest_float(D*a⁻, D*a⁺)); @assert tz(A) ≥ 0
    B = T(simplest_float(D*b⁻, D*b⁺)); @assert tz(B) ≥ 0
    S = T(simplest_float(D*s⁻, D*s⁺)); @assert tz(S) ≥ 0
    # readjust factors of two
    q = min(tz(A)+p, tz(B)+p, tz(S), tz(D))
    if p ≠ q
        A = ldexp(A, p-q)
        B = ldexp(B, p-q)
    end
    if q ≠ 0
        S = ldexp(S, -q)
        D = ldexp(D, -q)
    end
    # check assertions
    @assert A/D == a
    @assert B/D == b
    @assert S/D == s
    @assert (B - A)/S == N
    # compute the grid unit
    G = gcdf(A, B, S)
    g = TwicePrecision(G)/TwicePrecision(D)
    A /= G; B /= G; S /= G
    # check that inputs are hit
    @assert tmul(A, g) == a
    @assert tmul(B, g) == b
    @assert tmul(S, g) == s
    # return range object
    FRange(A, S, N, g)
end
