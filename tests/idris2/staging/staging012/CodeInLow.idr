module CodeInLow

import Language.Staged
import Language.Staged.Low

-- Only Low code can be spliced into low code
f : Code Int -> Low Int
f c = [|| ~c + 1 ||]
