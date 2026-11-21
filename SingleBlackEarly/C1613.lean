import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1613 : checkSingleBlackFast (-36, -17) 19672 .north (20, 16) (-46, -8) = true := by
  decide +kernel

end LangtonsAnt
