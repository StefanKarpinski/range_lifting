"""
    decompose(x::AbstractFloat) -> (n, p, f)

Integer values `n` and `p` such that `x == n*exp2(p)`. The `f` value is a
boolean flag indicating whether `x - eps(x) < prevfloat(x)`.
"""
function decompose(x::Float16)::Tuple{Int16,Int16,Bool}
    n = reinterpret(UInt16, x)
    s = (n & 0x03ff) % Int16
    e = ((n & 0x7c00) >> 10) % Int16
    f = (s == 0 && e > 1)
    s |= Int16(e != 0) << 10
    s, e - 25 + (e == 0), f
end

function decompose(x::Float32)::Tuple{Int32,Int32,Bool}
    n = reinterpret(UInt32, x)
    s = (n & 0x007fffff) % Int32
    e = ((n & 0x7f800000) >> 23) % Int32
    f = (s == 0 && e > 1)
    s |= Int32(e != 0) << 23
    s, e - 150 + (e == 0), f
end

function decompose(x::Float64)::Tuple{Int64,Int64,Bool}
    n = reinterpret(UInt64, x)
    s = (n & 0x000fffffffffffff) % Int64
    e = ((n & 0x7ff0000000000000) >> 52) % Int64
    f = (s == 0 && e > 1)
    s |= Int64(e != 0) << 52
    s, e - 1075 + (e == 0), f
end

function ival(x::AbstractFloat)
    n, p, f = decompose(x)
    lo = 4n - 2 + f
    hi = 4n + 2
    z = min(trailing_zeros(lo), trailing_zeros(hi))
    lo >>= z
    hi >>= z
    p += z - 2
    if x < 0
        lo, hi = -hi, -lo
    end
    lo, hi, p
end

using Test

test_values(::Type{T}) where {T<:AbstractFloat} = [
    -one(T)
    +one(T)
    -zero(T)
    +zero(T)
    -1eps(zero(T))
    +1eps(zero(T))
    -2eps(zero(T))
    +2eps(zero(T))
    -3eps(zero(T))
    +3eps(zero(T))
    -floatmin(T)/2
    +floatmin(T)/2
    -floatmin(T)
    +floatmin(T)
    -floatmin(T)*2
    +floatmin(T)*2
    randn(T, 100)
]

for T in (Float16, Float32, Float64), x in test_values(T)
    # test decompose
    n, p, f = decompose(x)
    @test n isa Integer && sizeof(n) == sizeof(x)
    @test p isa Integer && sizeof(p) == sizeof(x)
    @test f isa Bool
    @test T(n*exp2(p)) == abs(x)
    d = signbit(x) ? -1 : 1
    @test nextfloat(x, d) == x + d*eps(x)
    @test prevfloat(x, d) == x - d*eps(x)/(1+f)
    # test ival
    S = T == Float16 ? Int16 :
        T == Float32 ? Int32 :
        T == Float64 ? Int64 : error()
    lo, hi, p = ival(x)
    if T == Float64
        p = big(p) # force promotion to BigFloat
    end
    if isodd(reinterpret(S, x))
        @test T(lo*exp2(p)) < x
        @test T(nextfloat(lo*exp2(p))) == x
        @test T(prevfloat(hi*exp2(p))) == x
        @test T(hi*exp2(p)) > x
    else
        @test T(prevfloat(lo*exp2(p))) < x
        @test T(lo*exp2(p)) == x
        @test T(hi*exp2(p)) == x
        @test T(nextfloat(hi*exp2(p))) > x
    end
end
