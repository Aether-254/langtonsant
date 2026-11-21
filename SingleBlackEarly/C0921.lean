import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0921 : checkSingleBlackFast (-11, 8) 19902 .north (9, -5) (-36, -2) = true := by
  decide +kernel

end LangtonsAnt
