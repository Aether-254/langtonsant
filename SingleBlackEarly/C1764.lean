import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1764 : checkSingleBlack (-51, -30) 14338 .north (19, 7) (-46, -18) = true := by
  decide +kernel

end LangtonsAnt
