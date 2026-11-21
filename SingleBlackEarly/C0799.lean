import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0799 : checkSingleBlackFast (23, -6) 13951 .west (-16, 2) (-23, -28) = true := by
  decide +kernel

end LangtonsAnt
