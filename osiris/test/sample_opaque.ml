type 'a iarray

external unsafe_of_array : 'a array -> 'a iarray = "%opaque"
external unsafe_to_array : 'a iarray -> 'a array = "%opaque"
