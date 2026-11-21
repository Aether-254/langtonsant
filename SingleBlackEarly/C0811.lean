import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0811 : checkSingleBlackFast (25, -5) 11420 .north (-4, 1) (-28, 3) = true := by
  decide +kernel

end LangtonsAnt
