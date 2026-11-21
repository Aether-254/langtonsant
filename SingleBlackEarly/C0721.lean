import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0721 : checkSingleBlackFast (7, -11) 14252 .north (-4, -1) (-28, 1) = true := by
  decide +kernel

end LangtonsAnt
