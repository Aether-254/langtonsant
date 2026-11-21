import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0521 : checkSingleBlackFast (-4, -7) 11616 .north (2, 0) (-28, -4) = true := by
  decide +kernel

end LangtonsAnt
