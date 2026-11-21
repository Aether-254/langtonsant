import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1648 : checkSingleBlack (-41, -19) 14857 .west (8, 17) (-37, -3) = true := by
  decide +kernel

end LangtonsAnt
