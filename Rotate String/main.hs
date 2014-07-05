import Data.List
listOfRotation :: String -> [String]
listOfRotation s = let nextRotation = (tail s)++[head s] in nextRotation:(listOfRotation nextRotation)

readStringNTimes :: Int -> IO ()
readStringNTimes 0 = return ()
readStringNTimes nTimes = do
    line <- getLine
    let rotations = take (length line) $ listOfRotation line
    putStrLn $ intercalate " " rotations
    readStringNTimes (nTimes - 1)

main = do
    strNumCases <- getLine
    let numCases = read strNumCases :: Int
    readStringNTimes numCases
