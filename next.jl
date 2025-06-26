function decompose(x::Float16)::NTuple{2,Int16}
    n = reinterpret(UInt16, x)
    s = (n & 0x03ff) % Int16
    e = ((n & 0x7c00) >> 10) % Int16
    s |= Int16(e != 0) << 10
    s, e - 25 + (e == 0)
end

function decompose(x::Float32)::NTuple{2,Int32}
    n = reinterpret(UInt32, x)
    s = (n & 0x007fffff) % Int32
    e = ((n & 0x7f800000) >> 23) % Int32
    s |= Int32(e != 0) << 23
    s, e - 150 + (e == 0)
end

function decompose(x::Float64)::NTuple{2,Int64}
    n = reinterpret(UInt64, x)
    s = (n & 0x000fffffffffffff) % Int64
    e = ((n & 0x7ff0000000000000) >> 52) % Int64
    s |= Int64(e != 0) << 52
    s, e - 1075 + (e == 0)
end

function ival(x::AbstractFloat)
    n, p = decompose(x)
    hi = 4n + 2
    lo = 4n - 2 + ispow2(n)
    z = min(trailing_zeros(hi), trailing_zeros(lo))
    hi >>= z
    lo >>= z
    p += z - 2
    flipsign(hi, x), flipsign(lo, x), p
end
