import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0424 : checkSingleBlackFast (18, 2) 4641 .west (-11, 2) (-16, -12) = true := by
  decide +kernel

end LangtonsAnt
