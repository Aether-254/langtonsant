import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0803 : checkSingleBlackFast (22, -4) 13336 .north (2, 4) (-28, 0) = true := by
  decide +kernel

end LangtonsAnt
