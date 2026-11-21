import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1973 : checkSingleBlackFast (-72, -46) 13252 .north (25, 17) (-51, -33) = true := by
  decide +kernel

end LangtonsAnt
