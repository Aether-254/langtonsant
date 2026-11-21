import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1452 : checkSingleBlack (-24, 0) 41832 .north (1, -12) (-3, -50) = true := by
  decide +kernel

end LangtonsAnt
