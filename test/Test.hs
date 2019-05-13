import Test.Tasty
import Test.Tasty.HUnit

import Algebraic.Optics
import Algebraic.Optics.Equality
import Control.Monad
import Data.IORef
import Data.Function

data Department = Department { _budget :: Int }
  deriving (Eq, Show)

data University a b = 
  University { _name :: String
             , _extras :: Maybe a
             , _departments :: IORef [Department]
             , _extras2 :: IORef (Either String b)}

name :: ALens' (University a b) String
name = lens _name (\s a -> s { _name = a })

extras :: ALens (University a c) (University b c) (Maybe a) (Maybe b)
extras = lens _extras (\s b -> s { _extras = b })

budget :: ALens' Department Int
budget = lens _budget (\s a -> s { _budget = a })

departments :: ALensIO' (University a b) [Department]
departments = mrefLensEq _departments

extras2 :: (Eq a, HasEquality (University c a) (University c b) (Either String a) (Either String b)) 
        => ALensIO (University c a) (University c b) (Either String a) (Either String b)
extras2 = prefLensEq _extras2 (\s b -> s { _extras2 = b } )

main :: IO ()
main = defaultMain $
  testCase "University data" $ do

    d <- newIORef [Department { _budget = 2 }, Department { _budget = 3 }]
    e2 <- newIORef (Right "Extra")
    let uni = University { _name = "MIT", _extras = Just "1", _extras2 = e2, _departments = d }

    uni <- uni & departments . traversed . budget %~! (* 2)

    assertEqualIO "department" [Department {_budget = 4},Department {_budget = 6}] $ uni ^.! departments

    assertEqual "uni name" "MIT" $ uni ^. name

    assertEqual "polymorphic set ioref & get" (Just True) $ (uni & extras .~ Just True) ^. extras

    uni <- uni & extras2 .~! Right True

    assertEqualIO "get set ioref" (Right True) $ uni ^.! extras2

    assertEqualIO "traversal / lens ioref" [4,6] $ uni ^..! departments . traversed . budget

    assertEqualIO "indexed traversal ioref" 
      [(0,Department {_budget = 4}),(1,Department {_budget = 6})]  
      (uni ^@..! departments . traversed)

    assertEqualIO "preview first ioref"  (Just 4) $ uni ^?! departments . traversed . budget

    assertEqual "preview Just ioref" (Just "1") $ uni ^? extras . _Just
    assertEqual "preview Nothing ioref" Nothing   $ uni ^? extras . _Nothing
    assertEqual "review Just" (Just True) $ _Just # True
    assertEqual "review Nothing" (Nothing :: Maybe ()) $ _Nothing # ()
    assertEqual "review Just . Nothing" (Just Nothing :: Maybe (Maybe ())) $ _Just . _Nothing # ()
    assertEqual "review Just . Just"  (Just (Just True)) $ _Just . _Just # True

assertEqualIO :: (Eq a, Show a) => String -> a -> IO a -> Assertion
assertEqualIO msg exp act = join (assertEqual msg <$> pure exp <*> act)