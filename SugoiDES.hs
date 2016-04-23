--module SugoiDES where

import Data.Char
import Data.Word
import Data.List.Split
import System.Exit


encrString :: String -> String -> String
encrString plaintext keyStr = 
    do longsToStr cipher
    where longsPl = padStrToLongs plaintext
          keys = generateKeys keyStr
          keysAr = take (length longsPl) $ cycle [keys]
          cipher = map (\x -> encrypt (fst x) (snd x)) $ zip longsPl keysAr

decrString :: String -> String -> String
decrString ciphertext keyStr = 
    do unpadLongsToStr plain
    where longsCi = strToLongs ciphertext
          keys = generateKeys keyStr
          keysAr = take (length longsCi) $ cycle [keys]
          plain = map (\x -> decrypt (fst x) (snd x)) $ zip longsCi keysAr


--pad text to be encoded
padStrToLongs :: String -> [Word64]
padStrToLongs str = do map chrsToLong $ chunksOf 8 padded
                 where padSize = (mod (length str) 8)
                       padded = str ++ pad padSize
    
--used by decode, do not pad
strToLongs :: String -> [Word64]
strToLongs str = map chrsToLong $ chunksOf 8 str        


--version used by encrypt 
--does not strip padding 
longsToStr :: [Word64] -> String
longsToStr longs = concat $ map longToChrs longs

--version used by decrypt
--pass string to unpad in reverse to prevent O(n^2)
unpadLongsToStr :: [Word64] -> String
unpadLongsToStr longs = do reverse $ unpad $ reverse padded
                        where padded = concat $ map longToChrs longs

--create padding to make input a multiple of blocksize (64)
pad :: Int -> String
pad n = '\1':(take (7-n) $ cycle ['\0'])

--strip padding (from front)
--pass string in backwards for intended use
unpad :: String -> String
unpad str = if '\NUL' == head str
            then unpad $ drop 1 str
            else drop 1 str


--convert 8 chars as a long
chrsToLong :: String -> Word64
chrsToLong chrs = foldl (\x -> \y -> x*256 + y) 0 $ map (\x -> fromIntegral (ord x)) chrs

--convert long to 8 chars
longToChrs :: Word64 -> String
longToChrs long = l2c long 8

l2c :: Word64 -> Int -> [Char]
l2c long 0 = []
l2c long n = (l2c (div long 256) (n-1)) ++ [chr (fromIntegral (mod long 256))] 


--key generation
generateKeys :: String -> [[Bool]]
generateKeys keyStr = genKeys 16 (permute pc1 (hashStr keyStr))

genKeys :: Int -> [Bool] -> [[Bool]]
genKeys 0 mainKey = []
genKeys n mainKey = let shiftn = shiftValues !! (16-n)
                        shiftedl = leftShift shiftn (take 28 mainKey)
                        shiftedr = leftShift shiftn (drop 28 mainKey)
                        shifted = shiftedl ++ shiftedr
                    in (permute pc2 shifted):(genKeys (n-1) shifted)

--naiive hashing implementation
hashStr :: String -> [Bool]
hashStr str = do longToBools $ foldl hsh 1125899906842589 $ map ord64 str
              where hsh a b = a*31 + b
                    ord64 c = fromIntegral $ ord c

--encrypt / decrypt perform same operation but in reverse order
encrypt :: Word64 -> [[Bool]] -> Word64
encrypt plaintext keys = 
    do boolsToLong $ permute iip ciphertext
    where ciphertext = encr [0..15] keys $ permute ip $ longToBools plaintext

decrypt :: Word64 -> [[Bool]] -> Word64
decrypt ciphertext keys = 
    do boolsToLong $ permute iip plaintext
    where plaintext = encr [15,14..0] keys $ permute ip $ longToBools ciphertext

--do not swap halves on final round
encr :: [Int] -> [[Bool]] -> [Bool] -> [Bool]
encr round keys cipher = 
    do if 1 == length round
       then feis
       else encr (drop 1 round) keys $ (drop nDrop feis) ++ (take nDrop feis)
    where feis = fK cipher $ keys !! head round
          nDrop = div (length feis) 2

--leftshift used on each half of key
leftShift :: Int -> [Bool] -> [Bool]
leftShift n lst = do concat [drop n_ lst, take n_ lst]
                  where n_ = mod n (length lst)

--permute
permute :: [Int] -> [Bool] -> [Bool]
permute table inputList = do
    if null table 
    then []
    else x:xs 
    where x = inputList !! (head table)
          xs = (permute (drop 1 table) inputList)


--Perform fK round, 
-- L ^ feistel(R,Kx), R
fK :: [Bool] -> [Bool] -> [Bool]
fK dataBl subKey = 
    do newLeft ++ right
    where size = (div (length dataBl) 2)
          left = take size dataBl
          right = drop size dataBl
          newLeft = boolsXOR left $ feistel right subKey 


--Perform feistel round on right half of key
feistel :: [Bool] -> [Bool] -> [Bool]
feistel right subKey = 
    do permute p rawResult
    where epRight = boolsXOR subKey $ permute ep right
          sBoxInput = zip [0..7] $ chunksOf 6 epRight
          rawResult = concat $ map (\x -> sBoxLookup (snd x) (fst x)) sBoxInput


--convert long to bools
longToBools :: Word64 -> [Bool]
longToBools val = l2b val 64 

l2b :: Word64 -> Int -> [Bool]
l2b val 0 = []
l2b val bits = (l2b (div val 2) (bits-1)) ++ [((mod val 2) /= 0)] 


--XOR two lists of bools
boolsXOR :: [Bool] -> [Bool] -> [Bool]
boolsXOR a b = map (\x -> fst x /= snd x) $ zip a b

--convert bools to Nums
boolsToLong :: [Bool] -> Word64
boolsToLong bls = foldl (\x -> \y -> x*2 + y) 0 $ map (\x -> if x then 1 else 0) bls


--lookup value in Substitution Box
sBoxLookup :: [Bool] -> Int -> [Bool]
sBoxLookup bitArr index = let row = fromIntegral $ boolsToLong $ [(head bitArr), (last bitArr)]
                              col = fromIntegral $ boolsToLong $ tail (take 5 bitArr)
                              lookup = sBoxes !! index !! row !! col
                          in l2b lookup 4


-----------------
-------I/O-------
-----------------

printBools :: [Bool] -> IO ()
printBools bls = putStrLn $ map (\x -> if x then '1' else '0') bls


main :: IO ()
main = do 
    putStrLn "Choose [E]ncrypt or [D]ecrypt mode (or EXIT)"
    mode <- getLine
    if (map toUpper mode) == "EXIT"
    then exitSuccess
    else do
        putStrLn "Enter name of file to {En,De}code"
        input <- getLine
        putStrLn "Enter name of output file"
        out <- getLine
        putStrLn "Enter Key"
        key <- getLine
        fileStr <- readFile input
        case (toUpper $ head mode) of
            'E' -> writeFile out $ encrString fileStr key
            'D' -> writeFile out $ decrString fileStr key
        main



----------------------------------------------------------------
-----------------------DES Constants----------------------------
----------------------------------------------------------------
--Constants as retreived from Wikipedia:------------------------
-- http://en.wikipedia.org/wiki/DES_supplementary_material -----
--where applicable, some of the Substitution box values---------
--have been decremented to be zero based rather than one based--
----------------------------------------------------------------


--amount to left shift mainkey by each round
shiftValues = [1, 1, 2, 2, 2, 2, 2, 2, 
               1, 2, 2, 2, 2, 2, 2, 1]

--P is used to permute output of feistel
p = [15,  6, 19, 20, 28, 11, 27, 16,
      0, 14, 22, 25,  4, 17, 30,  9,
      1,  7, 23, 13, 31, 26,  2,  8,
     18, 12, 29,  5, 21, 10,  3, 24]

--Initial Permutation
--IP is performed on Plaintext: 'P' before commencing rounds
ip = [57, 49, 41, 33, 25, 17,  9, 1,
      59, 51, 43, 35, 27, 19, 11, 3,   
      61, 53, 45, 37, 29, 21, 13, 5,
      63, 55, 47, 39, 31, 23, 15, 7,
      56, 48, 40, 32, 24, 16,  8, 0,
      58, 50, 42, 34, 26, 18, 10, 2,
      60, 52, 44, 36, 28, 20, 12, 4,
      62, 54, 46, 38, 30, 22, 14, 6]

--Inverse Initial Permutation
--IP^-1 Inverse of IP, used after last round to permutate
--final ciphertext: 'C'
iip = [39, 7, 47, 15, 55, 23, 63, 31,
       38, 6, 46, 14, 54, 22, 62, 30,
       37, 5, 45, 13, 53, 21, 61, 29,
       36, 4, 44, 12, 52, 20, 60, 28,
       35, 3, 43, 11, 51, 19, 59, 27,
       34, 2, 42, 10, 50, 18, 58, 26,
       33, 1, 41,  9, 49, 17, 57, 25,
       32, 0, 40,  8, 48, 16, 56, 24] 

--Expansion
--EP is used to expand a 32bit half of plaintext to 48bit value
ep = [31,  0,  1,  2,  3,  4,
       3,  4,  5,  6,  7,  8,
       7,  8,  9, 10, 11, 12,
      11, 12, 13, 14, 15, 16,
      15, 16, 17, 18, 19, 20,
      19, 20, 21, 22, 23, 24,
      23, 24, 25, 26, 27, 28,
      27, 28, 29, 30, 31,  0]

--Permuted choice 2
--PC2 is used on 56bit LS(K) to generate 48bit subKeys
pc2 = [13, 16, 10, 23,  0,  4,  2, 27,
       14,  5, 20,  9, 22, 18, 11,  3,
       25,  7, 15,  6, 26, 19, 12,  1,
       40, 51, 30, 36, 46, 54, 29, 39,
       50, 44, 32, 47, 43, 48, 38, 55,
       33, 52, 45, 41, 49, 35, 28, 31]

--Permuted Choice 1
--PC1 is used to reduce 64bit key (K) to 56bit
pc1 = [56, 48, 40, 32, 24, 16,  8,
        0, 57, 49, 41, 33, 25, 17,
        9,  1, 58, 50, 42, 34, 26,
       18, 10,  2, 59, 51, 43, 35,
       62, 54, 46, 38, 30, 22, 14,
        6, 61, 53, 45, 37, 29, 21,
       13,  5, 60, 52, 44, 36, 28,
       20, 12,  4, 27, 19, 11,  3]

--Substitution boxes
sBoxes = [ --S0
          [[14,  4, 13,  1,  2, 15, 11,  8,  3, 10,  6, 12,  5,  9,  0,  7],
           [ 0, 15,  7,  4, 14,  2, 13,  1, 10,  6, 12, 11,  9,  5,  3,  8],
           [ 4,  1, 14,  8, 13,  6,  2, 11, 15, 12,  9,  7,  3, 10,  5,  0],
           [15, 12,  8,  2,  4,  9,  1,  7,  5, 11,  3, 14, 10,  0,  6, 13]],
           --S1
          [[15,  1,  8, 14,  6, 11,  3,  4,  9,  7,  2, 13, 12,  0,  5, 10],
           [ 3, 13,  4,  7, 15,  2,  8, 14, 12,  0,  1, 10,  6,  9, 11,  5],
           [ 0, 14,  7, 11, 10,  4, 13,  1,  5,  8, 12,  6,  9,  3,  2, 15],
           [13,  8, 10,  1,  3, 15,  4,  2, 11,  6,  7, 12,  0,  5, 14,  9]],
           --S2
          [[10,  0,  9, 14,  6,  3, 15,  5,  1, 13, 12,  7, 11,  4,  2,  8],
           [13,  7,  0,  9,  3,  4,  6, 10,  2,  8,  5, 14, 12, 11, 15,  1],
           [13,  6,  4,  9,  8, 15,  3,  0, 11,  1,  2, 12,  5, 10, 14,  7],
           [ 1, 10, 13,  0,  6,  9,  8,  7,  4, 15, 14,  3, 11,  5,  2, 12]],
           --S3
          [[ 7, 13, 14,  3,  0,  6,  9, 10,  1,  2,  8,  5, 11, 12,  4, 15],
           [13,  8, 11,  5,  6, 15,  0,  3,  4,  7,  2, 12,  1, 10, 14,  9],
           [10,  6,  9,  0, 12, 11,  7, 13, 15,  1,  3, 14,  5,  2,  8,  4],
           [ 3, 15,  0,  6, 10,  1, 13,  8,  9,  4,  5, 11, 12,  7,  2, 14]],
           --S4
          [[ 2, 12,  4,  1,  7, 10, 11,  6,  8,  5,  3, 15, 13,  0, 14,  9],
           [14, 11,  2, 12,  4,  7, 13,  1,  5,  0, 15, 10,  3,  9,  8,  6],
           [ 4,  2,  1, 11, 10, 13,  7,  8, 15,  9, 12,  5,  6,  3,  0, 14],
           [11,  8, 12,  7,  1, 14,  2, 13,  6, 15,  0,  9, 10,  4,  5,  3]],
           --S5
          [[12,  1, 10, 15,  9,  2,  6,  8,  0, 13,  3,  4, 14,  7,  5, 11],
           [10, 15,  4,  2,  7, 12,  9,  5,  6,  1, 13, 14,  0, 11,  3,  8],
           [ 9, 14, 15,  5,  2,  8, 12,  3,  7,  0,  4, 10,  1, 13, 11,  6],
           [ 4,  3,  2, 12,  9,  5, 15, 10, 11, 14,  1,  7,  6,  0,  8, 13]],
           --S6
          [[ 4, 11,  2, 14, 15,  0,  8, 13,  3, 12,  9,  7,  5, 10,  6,  1],
           [13,  0, 11,  7,  4,  9,  1, 10, 14,  3,  5, 12,  2, 15,  8,  6],
           [ 1,  4, 11, 13, 12,  3,  7, 14, 10, 15,  6,  8,  0,  5,  9,  2],
           [ 6, 11, 13,  8,  1,  4, 10,  7,  9,  5,  0, 15, 14,  2,  3, 12]],
           --S7
          [[13,  2,  8,  4,  6, 15, 11,  1, 10,  9,  3, 14,  5,  0, 12,  7],
           [ 1, 15, 13,  8, 10,  3,  7,  4, 12,  5,  6, 11,  0, 14,  9,  2],
           [ 7, 11,  4,  1,  9, 12, 14,  2,  0,  6, 10, 13, 15,  3,  5,  8],
           [ 2,  1, 14,  7,  4, 10,  8, 13, 15, 12,  9,  0,  3,  5,  6, 11]]
         ]
