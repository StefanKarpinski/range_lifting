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

# pick value in interval with the most trailing zeros
function simplest_float(lo::T, hi::T) where {T<:AbstractFloat}
    lo == hi && return lo
    hi < 0 && return -simplest_float(-hi, -lo)
    lo ≤ 0 && return zero(T)
    @assert 0 < lo < hi
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
    c::T
    d::T
    n::T
    g::TwicePrecision{T}
end

Base.length(r::FRange) = max(0, Int(r.n) + 1)
Base.first(r::FRange) = r[1]
Base.step(r::FRange) = tmul(r.d, r.g)
Base.last(r::FRange) = eltype(r)((r.n*r.d + r.c)*r.g)

Base.getindex(r::FRange{T}, i::Integer) where {T<:AbstractFloat} =
    T((TwicePrecision{T}(i-1)*r.d + r.c)*r.g)

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
        end
    end
end

# Find simple integers for length n and integers (c, d, e) such that:
#
#   n = (e - c)/d
#   c/d ∈ [a]/[s]
#   e/d ∈ [b]/[s]
#   c/e ∈ [a]/[b]
#
function range_ratios(a::T, s::T, b::T) where {T<:AbstractFloat}
    # handle negative step
    if signbit(s)
        a = -a
        s = -s
        b = -b
    end
    # double precision intervals for a, s, b
    a⁻, a⁺ = ival(a)
    s⁻, s⁺ = ival(s)
    b⁻, b⁺ = ival(b)
    # end-point/step ratio intervals
    r_a⁻ = ratio_break⁻(a⁻, signbit(a) ? s⁻ : s⁺)
    r_a⁺ = ratio_break⁺(a⁺, signbit(a) ? s⁺ : s⁻)
    r_b⁻ = ratio_break⁻(b⁻, signbit(b) ? s⁻ : s⁺)
    r_b⁺ = ratio_break⁺(b⁺, signbit(b) ? s⁺ : s⁻)
    # pick simplest range length
    n = T(simplest_float(r_b⁻ - r_a⁺, r_b⁺ - r_a⁻))
    # check if end-point can be hit
    p = tz(n)
    p ≥ 0 || error("end-point can't be hit (length)")
    # ratio intervals between end-points
    @sign_swap a b
    r_ab⁻ = ratio_break⁻(a⁻, b⁺)
    r_ab⁺ = ratio_break⁺(a⁺, b⁻)
    r_ba⁻ = ratio_break⁻(b⁻, a⁺)
    r_ba⁺ = ratio_break⁺(b⁺, a⁻)
    if signbit(a) ⊻ signbit(b)
        r_ab⁻, r_ab⁺ = -r_ab⁺, -r_ab⁻
        r_ba⁻, r_ba⁺ = -r_ba⁺, -r_ba⁻
    end
    @sign_swap a b
    # contract intervals based on identities
    for _ = 1:2
        if !iszero(a)
            # identity: r_a == n/(r_ba - 1)
            @update r_a⁻ < ratio_break⁻(n, r_ba⁺ - 1) # @show r_a⁻
            @update r_a⁺ > ratio_break⁺(n, r_ba⁻ - 1) # @show r_a⁺
        end
        if !iszero(b)
            # identity: r_b == n/(1 - r_ab)
            @update r_b⁻ < ratio_break⁻(n, 1 - r_ab⁻) # @show r_b⁻
            @update r_b⁺ > ratio_break⁺(n, 1 - r_ab⁺) # @show r_b⁺
        end
        for _ = 1:2
            # identity: r_a == r_b - n
            @update r_a⁻ < r_b⁻ - n # @show r_a⁻
            @update r_a⁺ > r_b⁺ - n # @show r_a⁺
            # identity: r_b == r_a + n
            @update r_b⁻ < r_a⁻ + n # @show r_b⁻
            @update r_b⁺ > r_a⁺ + n # @show r_b⁺
        end
        if !iszero(a)
            # identity: r_ba = 1 + n/r_a
            @update r_ba⁻ < 1 + n/r_a⁺
            @update r_ba⁺ > 1 + n/r_a⁻
            # identity: r_ab = 1/r_ba
            @update r_ab⁻ < inv(r_ba⁺)
            @update r_ab⁺ > inv(r_ba⁻)
        end
        if !iszero(b)
            # identity: r_ab = 1 - n/r_b
            @update r_ab⁻ < 1 - n/r_b⁻
            @update r_ab⁺ > 1 - n/r_b⁺
            # identity: r_ba = 1/r_ab
            @update r_ba⁻ < inv(r_ab⁺)
            @update r_ba⁺ > inv(r_ab⁻)
        end
    end
    # find fraction interval based on [a]
    f_a⁻, f_a⁺ = r_a⁻, r_a⁺
    f_a⁻ *= exp2(-p); f_a⁺ *= exp2(-p)
    q_a = round(prevfloat(f_a⁻), RoundDown)
    f_a⁻ -= q_a; f_a⁺ -= q_a
    # find fraction interval based on [b]
    f_b⁻, f_b⁺ = r_b⁻, r_b⁺
    f_b⁻ *= exp2(-p); f_b⁺ *= exp2(-p)
    q_b = round(prevfloat(f_b⁻), RoundDown)
    f_b⁻ -= q_b; f_b⁺ -= q_b
    # combine them
    f⁻ = max(f_a⁻, f_b⁻)
    f⁺ = max(f_a⁺, f_b⁺)
    f⁻ ≤ f⁺ || error("end-point can't be hit (ratios)")
    # find simplest rational in interval
    f_n, f_d = simplest_rational_core(f⁻, f⁺)
    d = T(f_d)
    # find simplest end-point ratios
    c = T(simplest_float(d*r_a⁻, d*r_a⁺))
    e = T(simplest_float(d*r_b⁻, d*r_b⁺))
    # eliminate common powers of two
    z = min(tz(c), tz(d), tz(e))
    @assert z ≥ -p
    t = exp2(-z)
    c *= t; d *= t; e *= t
    # check consistency
    @assert d*n == e - c
    # check ratios
    @sign_swap a b
    # check that c/d ∈ [a]/[s]
    @assert a⁻*abs(d) ≤ s⁺*abs(c)
    @assert a⁺*abs(d) ≥ s⁻*abs(c)
    # check that e/d ∈ [b]/[s]
    @assert b⁻*abs(d) ≤ s⁺*abs(e)
    @assert b⁺*abs(d) ≥ s⁻*abs(e)
    # check that c/e ∈ [a]/[b]
    @assert a⁻*abs(e) ≤ b⁺*abs(c)
    @assert a⁺*abs(e) ≥ b⁻*abs(c)
    @sign_swap a b
    # return values
    return n, c, d, e
end

function lift_range(a::T, s::T, b::T) where {T<:AbstractFloat}
    # normalize the range
    if any(issubnormal, (a, s, b))
        ε = eps(zero(T))
        r = lift_range(a/ε, s/ε, b/ε)
        return FRange(r.c, r.d, r.n, r.g*ε)
    end
    # find the relative grid ratios
    n, c, d, e = range_ratios(a, s, b)
    # still need rational value g:
    #  - g = s/d = a/c = b/e
    # get double precision bounds on g:
    lo_a, hi_a = ratio_ival(a, c)
    lo_s, hi_s = ratio_ival(s, d)
    lo_b, hi_b = ratio_ival(b, e)
    lo = max(lo_a, lo_s, lo_b)
    hi = min(hi_a, hi_s, hi_b)
    lo ≤ hi || error("end-point can't be hit (grid unit)")
    num, den = simplest_rational(lo, hi)
    g = num/den
    @assert lo ≤ g ≤ hi
    # check that inputs are hit
    @assert tmul(c, g) == a
    @assert tmul(d, g) == s
    @assert tmul(e, g) == b
    # return range object
    FRange(c, d, n, g)
end
