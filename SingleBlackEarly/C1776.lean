import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1776 : checkSingleBlackFast2 (-55, -28) 18522 .north (19, 12) (-46, -25) = true := by
  decide +kernel

end LangtonsAnt
