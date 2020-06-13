module Debug.Buffer

import Data.Buffer
import Data.List

toHex : Int -> String
toHex n = pack $ reverse (foldl toHexDigit [] (slice n))
    where
        toHexDigit : List Char ->Int -> List Char
        toHexDigit acc i = chr (if i < 10 then i + ord '0' else i + ord 'a')::acc
        slice : Int -> List Int
        slice 0 = []
        slice n = n `mod` 16::(slice (n `div` 16))

showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

renderRow : List Int -> String
renderRow dat = showSep " " (map toHex dat) ++ "\n"

group : Nat -> List a -> List (List a)
group n xs = worker [] xs
    where
        worker : List (List a) -> List a -> List (List a)
        worker acc [] = reverse acc
        worker acc ys = worker ((take n ys)::acc) (drop n ys)

export
dumpBuffer : Buffer -> IO String
dumpBuffer buf = do
    size <- rawSize buf
    dat <- bufferData buf
    let rows = group 16 dat
    let hex = showSep "\n" (map renderRow rows)
    pure $ hex ++ "\n\ntotal size = " ++ show size

export
printBuffer : Buffer -> IO ()
printBuffer buf = putStrLn $ !(dumpBuffer buf)