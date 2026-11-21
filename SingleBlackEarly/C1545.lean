import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1545 : checkSingleBlackFast (-31, -11) 23252 .north (8, 1) (-42, -21) = true := by
  decide +kernel

end LangtonsAnt
