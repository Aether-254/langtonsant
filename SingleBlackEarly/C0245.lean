import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0245 : checkSingleBlackFast (11, 5) 4865 .west (-3, 4) (-16, -4) = true := by
  decide +kernel

end LangtonsAnt
