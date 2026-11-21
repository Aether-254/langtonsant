import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1858 : checkSingleBlackFast2 (-58, -38) 15924 .north (24, 14) (-50, -30) = true := by
  decide +kernel

end LangtonsAnt
