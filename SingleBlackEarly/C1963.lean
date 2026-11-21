import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1963 : checkSingleBlack (-69, -49) 45890 .north (46, 29) (-73, -12) = true := by
  decide +kernel

end LangtonsAnt
