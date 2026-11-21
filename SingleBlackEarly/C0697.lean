import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0697 : checkSingleBlackFast (22, -10) 13284 .north (1, -2) (-25, -2) = true := by
  decide +kernel

end LangtonsAnt
