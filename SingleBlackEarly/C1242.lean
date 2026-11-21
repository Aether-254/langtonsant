import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1242 : checkSingleBlack (13, 18) 13856 .south (-12, -3) (-26, -9) = true := by
  decide +kernel

end LangtonsAnt
