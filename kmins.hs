import Control.Monad

kmins :: Int -> [a] -> [[a]]
kmins 0 _ = [[]]
kmins n l = l >>= \x -> map (x:) small
        where small = kmins (n-1) l

allminsets :: [a] -> [[a]]
allminsets l = join $ iterate go [[]]
        where go ls = do x <- l
                         fmap (x:) ls
