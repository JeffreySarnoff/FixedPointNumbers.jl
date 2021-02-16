# utility functions and macros, which are independent of `FixedPoint`
bitwidth(T::Type) = 8sizeof(T)

widen1(T::Type)         = T # fallback
widen1(::Type{Int8})    = Int16
widen1(::Type{UInt8})   = UInt16
widen1(::Type{Int16})   = Int32
widen1(::Type{UInt16})  = UInt32
widen1(::Type{Int32})   = Int64
widen1(::Type{UInt32})  = UInt64
widen1(::Type{Int64})   = Int128
widen1(::Type{UInt64})  = UInt128
widen1(x::Integer) = x % widen1(typeof(x))

signedtype(::Type{T}) where {T <: Integer} = typeof(signed(zero(T)))

const ShortInts = Union{Int8, UInt8, Int16, UInt16}
const LongInts = Union{Int64, UInt64, Int128, UInt128, BigInt}

const ShorterThanInt = Int === Int32 ? ShortInts : Union{ShortInts, Int32, UInt32}
const NotBiggerThanInt = Union{ShorterThanInt, Int, UInt}
const NotBiggerThanInt64 = Union{ShortInts, Int32, UInt32, Int64, UInt64}
const SShorterThanInt = typeintersect(ShorterThanInt, Signed)
const UShorterThanInt = typeintersect(ShorterThanInt, Unsigned)

macro f32(x::Float64) # just for hexadecimal floating-point literals
    :(Float32($x))
end
macro exp2(n)
     :(_exp2(Val($(esc(n)))))
end
_exp2(::Val{N}) where {N} = exp2(N)

# these are defined in julia/float.jl or julia/math.jl, but not exported
significand_bits(::Type{Float32}) = 23
significand_bits(::Type{Float64}) = 52
exponent_bias(::Type{Float32}) = 127
exponent_bias(::Type{Float64}) = 1023

_unsafe_trunc(::Type{T}, x::Integer) where {T} = x % T
_unsafe_trunc(::Type{T}, x) where {T} = unsafe_trunc(T, x)
# issue #202, #211
_unsafe_trunc(::Type{T}, x::BigFloat) where {T <: Integer} = trunc(BigInt, x) % T

if !signbit(signed(unsafe_trunc(UInt, -12.345)))
    # a workaround for ARM (issue #134)
    function _unsafe_trunc(::Type{T}, x::AbstractFloat) where {T <: Integer}
        if T === UInt32
            copysign(unsafe_trunc(T, abs(x)), x)
        else
            unsafe_trunc(T, unsafe_trunc(signedtype(T), x))
        end
    end
end

wrapper(@nospecialize(T)) = Base.typename(T).wrapper

# these select the arithmetic modality (saturating or wrapping)
# for Normed types and for Fixed types, independently

"""
    math_saturates(T) where T is `Normed` or `Fixed`

Sets arithmetic with `Normed`, `Fixed` types to saturate.

Rather than wrap around, results that would have
overflowed or underflowed instead will stay as
floatmax(T) or as floatmin(T), as appropriate.
"""
function math_saturates(::Type{T}) where {T<:FixedPoint}
    if T <: Normed
        normed_math_saturates()
    elseif T <: Fixed
        fixed_math_saturates()
    else
        normed_math_saturates()
        fixed_math_saturates()
    end   
end

"""
    math_wraps(T)

where T is `Normed` or `Fixed` or `FixedPoint`

Sets arithmetic with `Normed`, `Fixed` types to wrap.

Results may overflow or underflow, wrapping around.
`Fixed` types change sign as they wrap.
`Normed` types change magnitude as they wrap.
"""
function math_wraps(::Type{T}) where {T<:FixedPoint}
    if T <: Normed
        normed_math_wraps()
    elseif T <: Fixed
        fixed_math_wraps()
    else
        normed_math_wraps()
        fixed_math_wraps()
    end   
end

function normed_math_saturates()
  for (F,S) in ((:abs, :saturating_abs), (:neg, :saturating_neg))
  	@eval $F(x::Normed) = $S(x)
  end
  for (F,S) in ((:(+), :saturating_add), (:(-), :saturating_sub),
  	         (:(*), :saturating_mul), (:(/), :saturating_fdiv),
  	         (:(%), :saturating_rem))
    @eval $F(x::Normed, y::Normed) = $S(x, y)
  end
  for (F,S) in ((:cld, :saturating_cld), (:fld, :saturating_fld),
  	            (:mod, :saturating_mod), (:div, :saturating_div))
    @eval $F(x::Normed, y::Normed) = $S(x, y)
  end
end

function normed_math_wraps()
  for (F,S) in ((:abs, :wrapping_abs), (:neg, :wrapping_neg))
  	@eval $F(x::Normed) = $S(x)
  end
  for (F,S) in ((:(+), :wrapping_add), (:(-), :wrapping_sub),
  	            (:(*), :wrapping_mul), (:(/), :wrapping_fdiv),
  	            (:(%), :wrapping_rem))
    @eval $F(x::Normed, y::Normed) = $S(x, y)
  end
  for (F,S) in ((:cld, :wrapping_cld), (:fld, :wrapping_fld),
  	            (:mod, :wrapping_mod), (:div, :wrapping_div))
    @eval $F(x::Normed, y::Normed) = $S(x, y)
  end
end

function fixed_math_saturates()
  for (F,S) in ((:abs, :saturating_abs), (:neg, :saturating_neg))
  	@eval $F(x::Fixed) = $S(x)
  end
  for (F,S) in ((:(+), :saturating_add), (:(-), :saturating_sub),
  	            (:(*), :saturating_mul), (:(/), :saturating_fdiv),
  	            (:(%), :saturating_rem))
    @eval $F(x::Fixed, y::Fixed) = $S(x, y)
  end
  for (F,S) in ((:cld, :saturating_cld), (:fld, :saturating_fld),
  	            (:mod, :saturating_mod), (:div, :saturating_div))
    @eval $F(x::Fixed, y::Fixed) = $S(x, y)
  end
end

function fixed_math_wraps()
  for (F,S) in ((:abs, :wrapping_abs), (:neg, :wrapping_neg))
  	@eval $F(x::Fixed) = $S(x)
  end
  for (F,S) in ((:(+), :wrapping_add), (:(-), :wrapping_sub),
  	            (:(*), :wrapping_mul), (:(/), :wrapping_fdiv),
  	            (:(%), :wrapping_rem))
    @eval $F(x::Fixed, y::Fixed) = $S(x, y)
  end
  for (F,S) in ((:cld, :wrapping_cld), (:fld, :wrapping_fld),
  	            (:mod, :wrapping_mod), (:div, :wrapping_div))
    @eval $F(x::Fixed, y::Fixed) = $S(x, y)
  end
end
