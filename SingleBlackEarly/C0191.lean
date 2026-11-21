import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0191 : checkSingleBlackFast (11, -1) 2173 .west (-10, 5) (-11, -11) = true := by
  decide +kernel

end LangtonsAnt
