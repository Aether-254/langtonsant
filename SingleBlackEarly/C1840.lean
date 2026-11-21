import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1840 : checkSingleBlackFast2 (-60, -32) 17097 .west (23, 29) (-49, 6) = true := by
  decide +kernel

end LangtonsAnt
