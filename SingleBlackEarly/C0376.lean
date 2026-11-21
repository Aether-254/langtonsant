import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0376 : checkSingleBlackFast (15, -2) 4113 .west (-11, 0) (-14, -12) = true := by
  decide +kernel

end LangtonsAnt
