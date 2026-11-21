import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1677 : checkSingleBlack (-43, -23) 41204 .south (15, 6) (-53, -18) = true := by
  decide +kernel

end LangtonsAnt
