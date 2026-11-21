import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1194 : checkSingleBlackFast2 (26, 2) 15116 .north (-6, 2) (-30, 4) = true := by
  decide +kernel

end LangtonsAnt
