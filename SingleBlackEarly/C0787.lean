import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0787 : checkSingleBlackFast (23, -10) 7509 .west (-18, 8) (-22, -19) = true := by
  decide +kernel

end LangtonsAnt
