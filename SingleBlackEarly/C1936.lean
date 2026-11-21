import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1936 : checkSingleBlack (-68, -44) 14827 .west (21, 31) (-50, 11) = true := by
  decide +kernel

end LangtonsAnt
