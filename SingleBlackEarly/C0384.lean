import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0384 : checkSingleBlackFast (15, 1) 8156 .north (1, -2) (-21, -12) = true := by
  decide +kernel

end LangtonsAnt
