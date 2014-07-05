{-# LANGUAGE BangPatterns #-}

import Data.Foldable (toList)
import Data.Sequence (fromList, index, update, Seq, (|>), (><), empty, length)
import Data.List (sort,intercalate,foldl')
import Data.Vector (Vector, (!), fromList, length, slice)
import Data.Maybe (isNothing)

readPairList :: Int -> IO [(Int,Int)]
readPairList 0 = return []
readPairList numEdges = do
    line <- getLine
    let u:p:_ = map (\s -> read s :: Int) (words line)
    tail <- readPairList (numEdges-1)
    return ((u,p):tail)

data BinaryTree a = BinaryTree (Maybe (BinaryTree a)) a (Maybe (BinaryTree a))

indexPairListFromList :: [a] -> [(a,Int)]
indexPairListFromList [] = []
indexPairListFromList lst = listWithStartingIndex lst 1
    where
        listWithStartingIndex [x] idx = [(x,idx)]
        listWithStartingIndex (x:xs) idx = (x,idx):(listWithStartingIndex xs (idx+1))

treeFromEdges numVertices edges = 
    let !sortedEdges = Data.List.sort edges in
    let !childrenList = foldl (\list (p,u) -> let (curParent,curList) = head list in
                                if (p == curParent) then
                                    (curParent,u:curList):(tail list)
                                else 
                                    (p,[u]):([(n,[])|n <- reverse [curParent+1..p-1]]++list)) [(1,[])] sortedEdges in
    let revList = reverse ([(p,[])|p <- reverse [(Prelude.length childrenList)+1..numVertices]]++childrenList) in
    let childrenVector = Data.Vector.fromList [list | (_,list) <- revList] in
    childrenVector

postOrderList nodeIdx nodeVec = 
    let children = nodeVec ! (nodeIdx-1) in
    let !childrenSequences = [postOrderList idx nodeVec| idx <- children] in
    let !sequence = (foldl (\ lst (lst2,_) -> lst><lst2) Data.Sequence.empty childrenSequences) |> nodeIdx in
    let !node_sizes = (foldl (\ lst (_,lst2) -> lst><lst2) Data.Sequence.empty childrenSequences) |> (Data.Sequence.length sequence) in
    (sequence, node_sizes)

mergeVector :: Ord a => Vector a -> Vector a -> Vector a
mergeVector v1 v2 = 
    let list1 = toList v1 in
    let list2 = toList v2 in
    Data.Vector.fromList (mergeList list1 list2)
    where
        mergeList [] list2 = list2
        mergeList list1 [] = list1
        mergeList list1@(x1:xs1) list2@(x2:xs2) = if (x1 <= x2) then (x1:(mergeList xs1 list2)) else (x2:(mergeList list1 xs2))


segmentTreeFromVector :: Ord a => Vector a -> BinaryTree (Vector a)
segmentTreeFromVector v = 
    segmentTreeInRange 0 ((Data.Vector.length v) - 1)
    where 
        segmentTreeInRange leftIdx rightIdx = let len = rightIdx - leftIdx + 1 in
            case len of
              --0 -> Nothing
              1 -> BinaryTree Nothing (Data.Vector.slice leftIdx 1 v) Nothing
              otherwise -> let halfLen = len `quot` 2 in
                           let !left  = segmentTreeInRange leftIdx (leftIdx+halfLen-1) in
                           let !right = segmentTreeInRange (leftIdx+halfLen) rightIdx in
                           let (BinaryTree _ !v1 _) = left in
                           let (BinaryTree _ !v2 _) = right in
                           let !rootVec = mergeVector v1 v2 in
                           BinaryTree (Just left) rootVec (Just right)

salarySegmentTree :: [Int] -> [Int] -> (BinaryTree (Vector (Int,Int)))
salarySegmentTree employeeList salaryList =
    let salaryVector = Data.Vector.fromList (indexPairListFromList salaryList) in
    let arrangedSalaryList = [salaryVector ! (num-1) | num <- employeeList] in
    let arrangedSalaryVector = Data.Vector.fromList arrangedSalaryList in
    segmentTreeFromVector arrangedSalaryVector

positionsWithinVec :: Ord a => a -> Vector a -> (Int,Maybe a)
positionsWithinVec value vec = if (vec ! 0) > value then (0,Nothing) else binarySearch 1 (Data.Vector.length vec)
    where
        binarySearch left right = if (left==right) then
            (
                let val = vec ! (left-1) in
                (left,Just val)
            )
            else (
                let mid = (left + right + 1) `quot` 2 in
                let midVal = vec ! (mid-1) in
                if (midVal > value) then
                    binarySearch left (mid-1)
                else (
                    binarySearch mid right
                )
            )

maxMaybe :: Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing v2 = v2
maxMaybe v1 Nothing = v1
maxMaybe (Just v1) (Just v2) = Just (max v1 v2)

findKthInVecList :: Int -> [Vector (Int,Int)] -> Maybe (Int,Int)
findKthInVecList k vecList = binarySearch 1 1000000000
    where
        binarySearch left right = 
            let mid = (left+right) `quot` 2 in
            let (numLess, numVal) = foldl (\(x,y) (a,b) -> (x+a, maxMaybe y b)) (0,Just (0,0)) [positionsWithinVec (mid,0) v | v <- vecList] in
            if (numLess == k) then (
                numVal
            ) else (
                if (numLess < k) then
                    binarySearch (mid+1) right
                else
                    binarySearch left (mid-1)
            )

queryKthSalaryInInterval :: Int -> (Int,Int) -> (BinaryTree (Vector (Int,Int))) -> Maybe (Int,Int)
queryKthSalaryInInterval k queryInterval segmentTree =
    let (BinaryTree _ rootVec _) = segmentTree in 
    let segments = (enumerateSegments 1 (Data.Vector.length rootVec) queryInterval segmentTree) in
    (findKthInVecList k segments)
    where
        enumerateSegments outStart outEnd interval tree = 
           let (queryStart,queryEnd) = interval in
           let (BinaryTree leftTree vec rightTree) = tree in
           if (and [queryStart <= outStart, outEnd <= queryEnd]) then 
                ([vec]) 
           else (
                if (or [outEnd < queryStart, outStart > queryEnd]) then 
                    ([])
                else ( 
                    let left  = if Data.Maybe.isNothing leftTree then 
                                    [] 
                                else (
                                    let Just ltree = leftTree in
                                    enumerateSegments outStart ((outStart+outEnd-1) `quot` 2) queryInterval ltree) in
                    let right = if Data.Maybe.isNothing rightTree then 
                                    [] 
                                else (
                                    let Just rtree = rightTree in
                                    enumerateSegments ((outStart+outEnd-1) `quot` 2 + 1) outEnd queryInterval rtree) in
                    left++right
                )
           )

solveQuery v k segmentTree sizeVec posVec =
    let endPos = (posVec ! (v-1)) in
    let nodeSize = (sizeVec ! (endPos-1)) in
    let startPos = endPos-(nodeSize-1) in
    let Just (_,idx) = queryKthSalaryInInterval k (startPos,endPos-1) segmentTree in
    idx

posSeqFromQueryList queryLst =
    let len = Prelude.length queryLst in
    let seq = Data.Sequence.fromList [1..len] in
    let res = foldl (\s1 (val,idx) -> update (val-1) idx s1) seq (indexPairListFromList queryLst) in
    res


 
main = do
    strNQ <- getLine
    let n:q:_ = map (\s -> read s :: Int) (words strNQ)
    edges <- readPairList (n-1)
    line <- getLine
    let salaries = map (\s -> read s :: Int) (words line)
    queries <- readPairList q
    let edgesRev = map (\(x,y) -> (y,x)) edges
    let (!queryVec, !sizeVec) = postOrderList 1 $ treeFromEdges n edgesRev
    let (!queryLst, !sizeLst) = (toList queryVec, toList sizeVec)
    --putStrLn $ show (Prelude.length queryLst)
    --putStrLn $ show (Prelude.length sizeLst)
    --putStrLn $ show "-----------------------------------------------"
    let sizeVec = Data.Vector.fromList $ sizeLst
    let posVec = Data.Vector.fromList $ toList $ posSeqFromQueryList $ queryLst 
    let !segmentTree = salarySegmentTree queryLst salaries
    let (!results,_) = Data.List.foldl' (\(!resultLst,lastNum) (v_pre,k) -> 
                                let v = v_pre+lastNum in 
                                let res = solveQuery v k segmentTree sizeVec posVec 
                                in (res:resultLst,res)) ([],0) queries
    --putStrLn $ show $ Prelude.length results
    let !resultStr = Data.List.intercalate "\n" [show r|r <- reverse results]
    let !len = Prelude.length resultStr
    --putStrLn $ show $ Prelude.length resultStr
    putStrLn resultStr
    --mapM_ putStrLn [show r|r<-results]
