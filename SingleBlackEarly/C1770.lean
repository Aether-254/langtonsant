import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1770 : checkSingleBlackFast2 (-50, -30) 15508 .north (20, 10) (-46, -26) = true := by
  decide +kernel

end LangtonsAnt
